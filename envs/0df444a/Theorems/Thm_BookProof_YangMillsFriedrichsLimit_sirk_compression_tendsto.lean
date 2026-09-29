-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_compression_tendsto
-- name    : BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:45.892361+00:00
-- url     : https://prove2.me/theorems/7a4edd6a-2aec-4524-8eb4-e7cc26a16e51
-- title:
--   The Lean 4 theorem `sirk_compression_tendsto` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_tendsto` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto (A : F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F)) (u : F) :
    Filter.Tendsto (fun n : ℕ => sirkCompression A v n u) Filter.atTop (nhds (A u)) := by sorry
