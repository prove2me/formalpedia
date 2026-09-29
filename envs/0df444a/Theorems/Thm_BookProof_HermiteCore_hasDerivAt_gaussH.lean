-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hasDerivAt_gaussH
-- name    : BookProof.HermiteCore.hasDerivAt_gaussH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:26:20.993953+00:00
-- url     : https://prove2.me/theorems/4b964eb8-b5da-4aa1-86b7-8cc438a444bf
-- title:
--   The Lean 4 theorem `hasDerivAt_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hasDerivAt_gaussH
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hasDerivAt_gaussH (x : ℝ) : HasDerivAt gaussH (-(x / 2) * gaussH x) x := by sorry
