-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_rademacherMean_dot_sq
-- name    : BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:27.682977+00:00
-- url     : https://prove2.me/theorems/b09891ad-3402-47fd-ad66-b8740a5e3d96
-- title:
--   `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq` (k : Fin d → ℝ) : rademacherMean (fun x => (dot (signVec x) k) ^ 2) = ∑ i, (k i) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq` (k : Fin d → ℝ) : rademacherMean (fun x => (dot (signVec x) k) ^ 2) = ∑ i, (k i) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq (k : Fin d → ℝ) :
    rademacherMean (fun x => (dot (signVec x) k) ^ 2) = ∑ i, (k i) ^ 2 := by sorry
