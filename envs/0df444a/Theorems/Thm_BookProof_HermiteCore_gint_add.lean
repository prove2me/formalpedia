-- Prove2me | Theorems.Thm_BookProof_HermiteCore_gint_add
-- name    : BookProof.HermiteCore.gint_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:26:32.031359+00:00
-- url     : https://prove2.me/theorems/83200a0f-01fa-4bd7-a838-a4e346b999c6
-- title:
--   The Lean 4 theorem `gint_add` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gint_add` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.gint_add
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.gint_add (p q : Polynomial ℝ) : gint (p + q) = gint p + gint q := by sorry
