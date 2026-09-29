-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_weylKrylov_bestApprox_antitone
-- name    : BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:21:03.474554+00:00
-- url     : https://prove2.me/theorems/8d0e7de7-166a-4ef4-a058-6cd5f5771043
-- title:
--   The Lean 4 theorem `weylKrylov_bestApprox_antitone` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylKrylov_bestApprox_antitone` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_antitone
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]








open BookProof.ChapterH5 BookProof.ChapterH9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_antitone (H : E →ₗ[ℂ] E) (v : E) {p q : ℕ} (hpq : p ≤ q) (u : E) :
    ‖u - (krylovSpan H v q).starProjection u‖ ≤ ‖u - (krylovSpan H v p).starProjection u‖ := by sorry
