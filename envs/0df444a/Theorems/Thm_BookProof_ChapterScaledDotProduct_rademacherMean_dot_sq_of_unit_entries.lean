-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_rademacherMean_dot_sq_of_unit_entries
-- name    : BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:48:14.571749+00:00
-- url     : https://prove2.me/theorems/458f8695-17bb-49b3-a208-046c2e74642e
-- title:
--   `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries` {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) : rademacherMean (fun x => (dot (signVec x) k) ^ 2) = (d : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries` {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) : rademacherMean (fun x => (dot (signVec x) k) ^ 2) = (d : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq_of_unit_entries {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) :
    rademacherMean (fun x => (dot (signVec x) k) ^ 2) = (d : ℝ) := by sorry
