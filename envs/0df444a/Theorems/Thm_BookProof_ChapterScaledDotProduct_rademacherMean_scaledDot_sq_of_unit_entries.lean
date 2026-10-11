-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_rademacherMean_scaledDot_sq_of_unit_entries
-- name    : BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:44:29.046834+00:00
-- url     : https://prove2.me/theorems/52f7904f-48cc-45a3-996a-bbfab7ceb310
-- title:
--   `BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries` (hd : 0 < d) {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) : rademacherMean (fun x => (scaledDot (signVe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries` (hd : 0 < d) {k : Fin d → ℝ} (hk : ∀ i, (k i) ^ 2 = 1) : rademacherMean (fun x => (scaledDot (signVec x) k) ^ 2) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries (hd : 0 < d) {k : Fin d → ℝ}
    (hk : ∀ i, (k i) ^ 2 = 1) :
    rademacherMean (fun x => (scaledDot (signVec x) k) ^ 2) = 1 := by sorry
