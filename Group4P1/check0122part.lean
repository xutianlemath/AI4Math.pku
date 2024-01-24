import Init.Prelude
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Matrix.RowCol

import Mathlib.Algebra.Invertible.Defs
----

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.Matrix


import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef

open BigOperators Matrix
open Matrix


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
def Bsucc (B: Matrix n n ℝ  )(s y : Matrix n Unit ℝ  ): Matrix n n ℝ   :=
  B - (1/(sᵀ  * B * s) 0 0) • (B * s * sᵀ * B) + (1/(yᵀ * s) 0 0) • (y * yᵀ)

def norm2 (v : Matrix n Unit ℝ ) : ℝ  :=
  (vᵀ * v) 0 0

theorem SMW (u v : Matrix n Unit ℝ) (h : 1 + vᵀ * u ≠ 0):
  (1 + u * vᵀ)⁻¹ = 1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ) := by
  sorry

theorem lemma1 (u v : Matrix n Unit ℝ) :
  det (1 + u * vᵀ) = det (1 + vᵀ * u) := by
  sorry



theorem lemma1' (u v : Matrix n Unit ℝ) (h : 1 + vᵀ * u ≠ 0) : (1 + u * vᵀ) * (1 + u * vᵀ)⁻¹ = 1 := by
  sorry

#check Matrix.det_fin_one


set_option maxHeartbeats 20000000
theorem lemma2 (u v x y : Matrix n (Fin 1) ℝ) (h : 1 + vᵀ * u ≠ 0) :
  det (1 + u * vᵀ + x * yᵀ) = (1 + ((vᵀ * u) 0 0)) * (1 + ((yᵀ * x) 0 0)) - ((vᵀ * x) 0 0) * ((yᵀ * u) 0 0) := by
    have h2 : 1 + u * vᵀ + x * yᵀ = (1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by
      symm
      rw [mul_add, ← mul_assoc]; rw [lemma1' u v h]; rw [mul_one, one_mul]
    have h3 : det (1 + u * vᵀ + x * yᵀ) = det (1 + vᵀ * u) * det (1 + yᵀ * (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * x) := by
      calc
        det (1 + u * vᵀ + x * yᵀ) = det ((1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))) := by rw [h2]
        _ = det (1 + u * vᵀ) * det (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by apply det_mul (1 + u * vᵀ) (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))
        _ = det (1 + vᵀ * u) * det (1 + (1 + u * vᵀ)⁻¹ * x * yᵀ) := by rw [lemma1 u v]; rw [← Matrix.mul_assoc]
        _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 + u * vᵀ)⁻¹ * x) := by rw [lemma1 ((1 + u * vᵀ)⁻¹ * x) y, ← Matrix.mul_assoc]
        _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * x) := by rw [SMW u v h]


  sorry
-- 1 + vᵀ * u : Matrix Unit Unit ℝ
#check Matrix.det_fin_one

theorem det_BFGS_update {B : Matrix n n ℝ } {s y : Matrix n Unit ℝ }{r : ℝ }(h1 : Bᵀ = B)(h2 : (yᵀ * s) 0 0 > (0:ℝ))(h3 : PosDef B):
    det (Bsucc B s y) = (det B) * ((yᵀ * s) 0 0) / ((sᵀ * B * s) 0 0):= by
    unfold PosDef at h3
    sorry



--theorem det_BFGS_update (Bk : matrix) (sk yk : vector) :
--  mat_det (BFGS_update Bk sk yk) =
    -- The theorem's statement would go here.
-- example tassoc {A B C: Matrix n Unit ℝ}: A * Bᵀ  *C = A * (Bᵀ * C) := by
--   rw[Matrix.mul_assoc]
