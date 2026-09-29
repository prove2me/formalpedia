-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_weylKrylov_bestApprox_tendsto_zero
-- name    : BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:21:17.578787+00:00
-- url     : https://prove2.me/theorems/de41118f-a7a1-49d1-b27f-8bbcb922e685
-- title:
--   The Lean 4 theorem `weylKrylov_bestApprox_tendsto_zero` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylKrylov_bestApprox_tendsto_zero` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_tendsto_zero
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]








open BookProof.ChapterH5 BookProof.ChapterH9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_tendsto_zero (H : E →ₗ[ℂ] E) (v u : E)
    (hdense : Dense ((⨆ k : ℕ, krylovSpan H v k : Submodule ℂ E) : Set E)) :
    Filter.Tendsto (fun k : ℕ => ‖u - (krylovSpan H v k).starProjection u‖)
      Filter.atTop (nhds 0) := by sorry
