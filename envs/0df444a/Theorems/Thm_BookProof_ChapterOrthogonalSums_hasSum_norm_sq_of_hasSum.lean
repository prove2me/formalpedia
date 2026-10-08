-- Prove2me | Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum
-- name    : BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:52:19.453468+00:00
-- url     : https://prove2.me/theorems/4be474a3-b330-4b90-ba8f-bde461cb6c64
-- title:
--   `BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum` {ι : Type*} {v : ι → E} {psi : E} (h : HasSum v psi) (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) : HasSum (fun x => ‖v x‖ ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOrthogonalSums`.
--
--   `BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum` {ι : Type*} {v : ι → E} {psi : E} (h : HasSum v psi) (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) : HasSum (fun x => ‖v x‖ ^ 2) (‖psi‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum`.

-- Generated from ChapterOrthogonalSums.lean — theorem BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
open BookProof.ChapterOrthogonalSums


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum {ι : Type*} {v : ι → E} {psi : E} (h : HasSum v psi)
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) :
    HasSum (fun x => ‖v x‖ ^ 2) (‖psi‖ ^ 2) := by sorry
