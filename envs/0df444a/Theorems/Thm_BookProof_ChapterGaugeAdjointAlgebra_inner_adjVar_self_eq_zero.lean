-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_inner_adjVar_self_eq_zero
-- name    : BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:52:49.350667+00:00
-- url     : https://prove2.me/theorems/12a8d09d-2bdf-4dda-a0a2-2ab399034b69
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero` {κ : L → L → ℝ} (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0) (hsymm : ∀ x y : L, κ x y = κ y x) (x θ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero` {κ : L → L → ℝ} (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0) (hsymm : ∀ x y : L, κ x y = κ y x) (x θ : L) : κ ⁅x, θ⁆ x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero {κ : L → L → ℝ}
    (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0)
    (hsymm : ∀ x y : L, κ x y = κ y x) (x θ : L) : κ ⁅x, θ⁆ x = 0 := by sorry
