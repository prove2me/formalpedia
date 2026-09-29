-- Prove2me | Theorems.Thm_BookProof_ChapterH9_krylov_bestApprox_tendsto_zero
-- name    : BookProof.ChapterH9.krylov_bestApprox_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:05.442167+00:00
-- url     : https://prove2.me/theorems/21ae6521-820f-4f02-91b7-afa66b4cd863
-- title:
--   The Lean 4 theorem `krylov_bestApprox_tendsto_zero` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylov_bestApprox_tendsto_zero` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.krylov_bestApprox_tendsto_zero
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.krylov_bestApprox_tendsto_zero (H : E →ₗ[ℂ] E) (v u : E)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan H v n : Submodule ℂ E) : Set E)) :
    Filter.Tendsto (fun n : ℕ => ‖u - (krylovSpan H v n).starProjection u‖)
      Filter.atTop (nhds 0) := by sorry
