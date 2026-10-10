-- Prove2me | Theorems.Thm_BookProof_ChapterOrthogonalSums_norm_sum_sq_of_orthogonal
-- name    : BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:03:57.017529+00:00
-- url     : https://prove2.me/theorems/cc6a6343-cfd2-4267-ac06-5bddf4c238ce
-- title:
--   `BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal` {ι : Type*} (t : Finset ι) {v : ι → E} (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) : ‖∑ x ∈ t, v x‖ ^ 2 = ∑...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOrthogonalSums`.
--
--   `BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal` {ι : Type*} (t : Finset ι) {v : ι → E} (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) : ‖∑ x ∈ t, v x‖ ^ 2 = ∑ x ∈ t, ‖v x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal`.

-- Generated from ChapterOrthogonalSums.lean — theorem BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
open BookProof.ChapterOrthogonalSums


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal {ι : Type*} (t : Finset ι) {v : ι → E}
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) :
    ‖∑ x ∈ t, v x‖ ^ 2 = ∑ x ∈ t, ‖v x‖ ^ 2 := by sorry
