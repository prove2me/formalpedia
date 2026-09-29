-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hasDerivAt_poly_mul_gaussH
-- name    : BookProof.HermiteCore.hasDerivAt_poly_mul_gaussH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:24:19.035547+00:00
-- url     : https://prove2.me/theorems/b5606f28-2bbb-4a90-9735-97ecebced280
-- title:
--   The Lean 4 theorem `hasDerivAt_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hasDerivAt_poly_mul_gaussH
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hasDerivAt_poly_mul_gaussH (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y * gaussH y)
      ((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x) x := by sorry
