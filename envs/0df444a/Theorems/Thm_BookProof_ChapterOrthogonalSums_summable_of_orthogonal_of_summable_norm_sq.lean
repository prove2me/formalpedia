-- Prove2me | Theorems.Thm_BookProof_ChapterOrthogonalSums_summable_of_orthogonal_of_summable_norm_sq
-- name    : BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:04:36.448534+00:00
-- url     : https://prove2.me/theorems/4b9c92bf-9e5f-4f48-8556-d2098bd763e6
-- title:
--   `BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq` [CompleteSpace E] {ι : Type*} {v : ι → E} (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) (hsum : Summable fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOrthogonalSums`.
--
--   `BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq` [CompleteSpace E] {ι : Type*} {v : ι → E} (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) (hsum : Summable fun x => ‖v x‖ ^ 2) : Summable v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq`.

-- Generated from ChapterOrthogonalSums.lean — theorem BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
open BookProof.ChapterOrthogonalSums


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq [CompleteSpace E] {ι : Type*} {v : ι → E}
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) (hsum : Summable fun x => ‖v x‖ ^ 2) :
    Summable v := by sorry
