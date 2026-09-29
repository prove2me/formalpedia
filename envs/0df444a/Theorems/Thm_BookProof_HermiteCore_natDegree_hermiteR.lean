-- Prove2me | Theorems.Thm_BookProof_HermiteCore_natDegree_hermiteR
-- name    : BookProof.HermiteCore.natDegree_hermiteR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:29:20.054568+00:00
-- url     : https://prove2.me/theorems/eaf9d439-72c5-4c37-af46-7c706336c4ac
-- title:
--   The Lean 4 theorem `natDegree_hermiteR` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `natDegree_hermiteR` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.natDegree_hermiteR
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.natDegree_hermiteR (n : ℕ) : (hermiteR n).natDegree = n := by sorry
