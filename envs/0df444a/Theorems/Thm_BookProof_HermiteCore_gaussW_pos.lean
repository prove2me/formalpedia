-- Prove2me | Theorems.Thm_BookProof_HermiteCore_gaussW_pos
-- name    : BookProof.HermiteCore.gaussW_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:26:27.172549+00:00
-- url     : https://prove2.me/theorems/92bc9b60-359c-4cde-8e3d-2de12c14ae4d
-- title:
--   The Lean 4 theorem `gaussW_pos` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussW_pos` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.gaussW_pos
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.gaussW_pos (x : ℝ) : 0 < gaussW x := by sorry
