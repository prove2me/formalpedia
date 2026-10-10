-- Prove2me | Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_smul_of_hasSum_norm_sq
-- name    : BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:04:09.054804+00:00
-- url     : https://prove2.me/theorems/3453a9d3-2d1e-4f00-a23b-867d4c5c8b5c
-- title:
--   `BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq` [CompleteSpace E] {ι : Type*} {v : ι → E} (hv : Orthonormal ℂ v) {y : E} (h : HasSum (fun k => ‖⟪v k, y⟫_ℂ‖ ^ 2) (‖y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOrthogonalSums`.
--
--   `BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq` [CompleteSpace E] {ι : Type*} {v : ι → E} (hv : Orthonormal ℂ v) {y : E} (h : HasSum (fun k => ‖⟪v k, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2)) : HasSum (fun k => ⟪v k, y⟫_ℂ • v k) y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq`.

-- Generated from ChapterOrthogonalSums.lean — theorem BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq
import Mathlib
import Definitions.Def_ChapterOrthogonalSums
open BookProof.ChapterOrthogonalSums


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq [CompleteSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℂ v) {y : E}
    (h : HasSum (fun k => ‖⟪v k, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2)) :
    HasSum (fun k => ⟪v k, y⟫_ℂ • v k) y := by sorry
