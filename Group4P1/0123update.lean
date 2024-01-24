import Init.Prelude
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Matrix.RowCol


import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.GroupAction.BigOperators
----

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open BigOperators Matrix
open Matrix
open scoped Matrix BigOperators

#check det_updateRow_add_smul_self
#check det_updateColumn_add_smul_self
-- 要用到的初等行/列变换
#check det_fromBlocks_zero₂₁
--2*2分块上三角行列式
#check BlockTriangular.det

#check det_blockDiagonal

#check det_fin_two_of

#check trace_transpose

#check trace_sum
#check trace_sub
#check trace_neg
#check trace_mul_comm
#check trace_smul

#check Matrix.ext_iff.mp
namespace Matrix
noncomputable section
open Finset



variable {m n : Type*} [DecidableEq n] [Fintype n]
variable {α : Type}
-- variable { A : Matrix n n ℝ}
-- variable {x z : Matrix n Unit ℝ}

#check frobenius_norm_def
#check trace
open InnerProductSpace Set
open Equiv Equiv.Perm Finset Function

#check ℝ

-- The BFGS update function could be defined in terms of these operations.
def Bsucc (B: Matrix n n ℝ  )(s y : Matrix n (Fin 1) ℝ  ): Matrix n n ℝ   :=
  B - (1/(sᵀ  * B * s) 0 0) • (B * s * sᵀ * B) + (1/(yᵀ * s) 0 0) • (y * yᵀ)

def norm2 (v : Matrix n (Fin 1) ℝ ) : ℝ  :=
  (vᵀ * v) 0 0

-- Theorems would be stated using these definitions.
theorem trace_BFGS_update {B : Matrix n n ℝ } {s y : Matrix n (Fin 1) ℝ } (h : Bᵀ = B):
  trace (Bsucc B s y) = trace ( B ) - (norm2 (B*s)) * (1/(sᵀ  * B * s) 0 0) + (norm2 y) * (1/(yᵀ * s) 0 0) := by
    unfold Bsucc
    rw[trace_add,trace_sub,trace_smul,trace_smul]
    have h': (1 / (sᵀ * B * s) 0 0) •  trace (B * s * sᵀ * B) = (norm2 (B*s))* (1/(sᵀ  * B * s) 0 0) := by
      have : trace (B * s * sᵀ * B) = norm2 (B*s) :=by
        rw[trace_mul_comm]
        rw[← Matrix.mul_assoc]
        rw[trace_mul_comm]
        rw[← Matrix.mul_assoc]
        have : sᵀ * B = (B * s)ᵀ :=by
          rw[Matrix.transpose_mul];rw[h]
        rw[this]
        unfold trace;unfold norm2;simp
      rw[this]
      simp;rw[mul_comm]
    have g': (1 / (yᵀ * s) 0 0) • trace (y * yᵀ) = (norm2 y) * (1/(yᵀ * s) 0 0) := by
      have : trace (y * yᵀ) = norm2 y:=by
        rw[trace_mul_comm]
        unfold trace;unfold norm2;simp
      rw[this]
      simp;rw[mul_comm]
    rw[h'];rw[g']

theorem SMW (u v : Matrix n (Fin 1) ℝ) (h : det (1 + vᵀ * u) ≠ 0):
  (1 + u * vᵀ)⁻¹ = 1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ) := by
    have h' : (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * (1 + u * vᵀ) = 1 :=by
      rw[sub_mul];rw[one_mul]
      have h'' : u * (1 + vᵀ * u)⁻¹ * vᵀ * (1 + u * vᵀ) = u * vᵀ :=by
        rw[mul_add];rw[← Matrix.mul_assoc];rw[mul_one]
        rw[Matrix.mul_assoc (u * (1 + vᵀ * u)⁻¹ * vᵀ) u vᵀ]
        rw[Matrix.mul_assoc (u * (1 + vᵀ * u)⁻¹) vᵀ (u * vᵀ)];rw[← Matrix.mul_assoc vᵀ u vᵀ]
        rw[← Matrix.mul_add];nth_rw 2 [← Matrix.one_mul vᵀ];rw[← Matrix.add_mul];rw[← Matrix.mul_assoc]
        have : (1 + vᵀ * u)⁻¹ * (1 + vᵀ * u) = 1 :=by
          rw[Matrix.nonsing_inv_mul];unfold IsUnit
          simp;by_contra h';apply h
          rw[Matrix.det_fin_one];exact h'
        rw[Matrix.mul_assoc];rw[Matrix.mul_assoc];rw[← Matrix.mul_assoc (1 + vᵀ * u)⁻¹ (1 + vᵀ * u) vᵀ];rw[this];rw[Matrix.one_mul]
      rw[h''];rw[← add_sub];rw[sub_self];rw[add_zero]
    apply Matrix.inv_eq_left_inv;exact h'

theorem lemma1 (u v : Matrix n (Fin 1) ℝ) :
  det (1 + u * vᵀ) = det (1 + vᵀ * u) := by
  simp
  let A := Matrix.fromBlocks 1 (-u) vᵀ 1
  let T1 := Matrix.fromBlocks (1:Matrix n n ℝ) u 0 (1:Matrix (Fin 1) (Fin 1) ℝ)
  let AT1 :=  A * T1
  have : AT1 = fromBlocks 1 0 vᵀ (1  + vᵀ * u) :=by
    simp;rw[Matrix.fromBlocks_multiply]
    apply Matrix.ext_iff_blocks.2
    constructor
    · simp
    · simp;rw[add_comm]
  have : det AT1 = det (1 + vᵀ * u) := by
    rw[this];rw[Matrix.det_fromBlocks_zero₁₂];rw[det_one]
    ring
  symm
  have : det AT1 = 1 + (vᵀ * u) 0 0 := by
    rw[this];simp
  rw[← this]
  have : det AT1 =  det A := by
    simp
  rw[this]
  let T2 := fromBlocks (1 : Matrix n n ℝ) u 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)
  let AT2 := T2 * A
  have : AT2 = fromBlocks (1 + u * vᵀ) 0 vᵀ 1 :=by
    simp;rw[Matrix.fromBlocks_multiply]
    apply Matrix.ext_iff_blocks.2
    constructor
    · simp
    · simp
  have : det AT2 = det (1 + u * vᵀ) := by
    rw[this];rw[Matrix.det_fromBlocks_zero₁₂];rw[det_one]
    ring
  symm;rw[← this]
  have : det AT2 = det A := by
    simp
  rw[this]

theorem lemma1' (u v : Matrix n (Fin 1) ℝ) (h : det (1 + vᵀ * u) ≠ 0) : (1 + u * vᵀ) * (1 + u * vᵀ)⁻¹ = 1 := by
  rw[Matrix.mul_nonsing_inv];unfold IsUnit
  simp;by_contra h';apply h;rw[← lemma1];exact h'


set_option maxHeartbeats 20000000
theorem lemma2 (u v x y : Matrix n (Fin 1) ℝ) (h : det (1 + vᵀ * u) ≠ 0) :
  det (1 + u * vᵀ + x * yᵀ) = (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u) 0 0) * (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + yᵀ * x) 0 0) - ((vᵀ * x) 0 0) * ((yᵀ * u) 0 0) := by
    have h2 : 1 + u * vᵀ + x * yᵀ = (1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by
      symm
      rw [mul_add, ← mul_assoc];rw [lemma1' u v h]; rw [mul_one, one_mul]
    have h3 : det (1 + u * vᵀ + x * yᵀ) = det (1 + vᵀ * u) * det (1 + yᵀ * x - yᵀ * u * (1 + vᵀ * u)⁻¹ * vᵀ * x) := by
      calc
        det (1 + u * vᵀ + x * yᵀ) = det ((1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))) := by rw [h2]
        _ = det (1 + u * vᵀ) * det (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by apply det_mul (1 + u * vᵀ) (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))
        _ = det (1 + vᵀ * u) * det (1 + (1 + u * vᵀ)⁻¹ * x * yᵀ) := by rw [lemma1 u v]; rw [← Matrix.mul_assoc]
        _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 + u * vᵀ)⁻¹ * x) := by rw [lemma1 ((1 + u * vᵀ)⁻¹ * x) y, ← Matrix.mul_assoc]
        _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * x) := by rw [SMW u v h]
        _ = det (1 + vᵀ * u) * det (1 + yᵀ * x - yᵀ * u * (1 + vᵀ * u)⁻¹ * vᵀ * x) :=by
          rw[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, add_sub, ← Matrix.mul_assoc,← Matrix.mul_assoc]
    rw[h3];rw[Matrix.det_fin_one];rw[Matrix.det_fin_one];rw[Matrix.sub_apply];rw[mul_sub]
    have : ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u) 0 0 * (yᵀ * u * ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)⁻¹ * vᵀ * x) 0 0 = ((vᵀ * x) 0 0) * ((yᵀ * u) 0 0) :=by
      rw[← Matrix.det_fin_one ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)];rw[← Matrix.det_fin_one (yᵀ * u * ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)⁻¹ * vᵀ * x)]
      rw[Matrix.mul_assoc];rw[Matrix.det_mul];rw[Matrix.det_mul];rw[← mul_assoc];rw[← mul_assoc];
      rw[mul_comm (det ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)) (det (yᵀ * u))]
      rw[mul_assoc (det (yᵀ * u)) (det (1 + vᵀ * u)) (det (1 + vᵀ * u)⁻¹)]
      rw[← Matrix.det_mul];rw[Matrix.mul_nonsing_inv];rw[Matrix.det_one]
      rw[mul_one, Matrix.det_fin_one, Matrix.det_fin_one];ring
      unfold IsUnit;simp;by_contra h';apply h;rw[Matrix.det_fin_one];exact h'
    rw[this]

#check det_smul
#check smul_comm
#check smul_mul
#check mul_smul

lemma lemma3 (u v : Matrix n (Fin 1) ℝ) : uᵀ * v = vᵀ * u := by
  refine ext ?_
  intro i j
  sorry

theorem det_BFGS_update {B : Matrix n n ℝ } {s y : Matrix n (Fin 1) ℝ }{r : ℝ }(h1 : Bᵀ = B)(h2 : (yᵀ * s) 0 0 > (0:ℝ))(h3 : PosDef B):
  det (Bsucc B s y) = (det B) * ((yᵀ * s) 0 0) / ((sᵀ * B * s) 0 0):= by
    unfold PosDef at h3
    have Bdetpos : 0 < det B := by exact Matrix.PosDef.det_pos h3
    have detB_unit : IsUnit (det B) := by unfold IsUnit; simp; by_contra h'; linarith [Bdetpos]
    have Binv : Invertible B := by apply Matrix.invertibleOfIsUnitDet B detB_unit
    have h4 : B * B⁻¹ = 1 := by rw[Matrix.mul_nonsing_inv]; exact detB_unit
    have h5 : B⁻¹ * B = 1 := by rw[Matrix.nonsing_inv_mul]; exact detB_unit
    have B_inv_symm : B⁻¹ᵀ = B⁻¹ := by sorry
    rcases h3 with ⟨_, h7⟩
    have h6 : 0 < (yᵀ * B⁻¹ * y) 0 0 := by
      have : yᵀ * B⁻¹ * y = (B⁻¹ * y)ᵀ * B * (B⁻¹ * y) := by
        rw[Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (yᵀ * B⁻¹ᵀ)]
        rw[h4, Matrix.mul_one, B_inv_symm]
      rw[this]
      sorry
    let u := (1 / (sᵀ * y) 0 0) • (B⁻¹ * y)
    let x := (1 / (sᵀ * B * s) 0 0) • s
    let z := - (B * s)
    have h' : det (1 + yᵀ * u) ≠ 0 := by
      rw[Matrix.det_fin_one]
      have c1 : 1 + yᵀ * u = 1 + ((1 / (sᵀ * y) 0 0) • (yᵀ * B⁻¹ * y)) := by
        calc
          1 + yᵀ * u = 1 + yᵀ * (1 / (sᵀ * y) 0 0) • (B⁻¹ * y) := by rfl
          _ = 1 + (1 / (sᵀ * y) 0 0) • (yᵀ * (B⁻¹ * y)) := by rw[mul_smul yᵀ (1 / (sᵀ * y) 0 0) (B⁻¹ * y)]
          _ = 1 + (1 / (sᵀ * y) 0 0) • (yᵀ * B⁻¹ * y) := by rw[← Matrix.mul_assoc]
      rw [c1]
      have c2 : 1 / (sᵀ * y) 0 0 > 0 := by
        have d1 : 1 / (sᵀ * y) 0 0 = ((sᵀ * y) 0 0)⁻¹ := by exact one_div ((sᵀ * y) 0 0)
        have d2 : 0 < 1 / (sᵀ * y) 0 0 := by rw [d1, lemma3 s y]; apply inv_pos_of_pos h2
        exact d2
      have c3 : ((1 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / (sᵀ * y) 0 0) • (yᵀ * B⁻¹ * y))) 0 0 = 1 + (1 / (sᵀ * y) 0 0) * ((yᵀ * B⁻¹ * y) 0 0) := by
        rw [Matrix.add_apply, Matrix.smul_apply]; rfl
      rw [c3]
      have c4 : 0 < (1 / (sᵀ * y) 0 0) * (yᵀ * B⁻¹ * y) 0 0 := by
        apply mul_pos c2 h6
      linarith [c4]
    have eq1 : (det B) * det (1 + u * yᵀ + x * zᵀ)
      = (det B) * ((1 + ((yᵀ * u) 0 0)) * (1 + ((zᵀ * x) 0 0)) - ((yᵀ * x) 0 0) * ((zᵀ * u) 0 0)) := by
        rw [lemma2 u y x z h']
    have eq2 : (det B) * det (1 + u * yᵀ + x * zᵀ) = det (Bsucc B s y) := by sorry
    have eq3 : ((1 + ((yᵀ * u) 0 0)) * (1 + ((zᵀ * x) 0 0)) - ((yᵀ * x) 0 0) * ((zᵀ * u) 0 0))
      = ((yᵀ * s) 0 0) / ((sᵀ * B * s) 0 0) := by sorry

    rw[← eq2, eq1, eq3]; ring




--theorem det_BFGS_update (Bk : matrix) (sk yk : vector) :
--  mat_det (BFGS_update Bk sk yk) =
    -- The theorem's statement would go here.
-- example tassoc {A B C: Matrix n Unit ℝ}: A * Bᵀ  *C = A * (Bᵀ * C) := by
--   rw[Matrix.mul_assoc]
