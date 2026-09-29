-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_krylov_starProjection_tendsto
-- name    : BookProof.YangMillsFriedrichsLimit.krylov_starProjection_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:20.101273+00:00
-- url     : https://prove2.me/theorems/8e789503-0877-465c-a134-d583214dabc4
-- title:
--   The Lean 4 theorem `krylov_starProjection_tendsto` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylov_starProjection_tendsto` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.krylov_starProjection_tendsto
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.krylov_starProjection_tendsto (A : F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F)) (u : F) :
    Filter.Tendsto (fun n : ℕ => (krylovSpan A.toLinearMap v n).starProjection u)
      Filter.atTop (nhds u) := by sorry
