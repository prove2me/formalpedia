-- Prove2me | Theorems.Thm_BookProof_HermiteCore_deriv_poly_mul_gaussH
-- name    : BookProof.HermiteCore.deriv_poly_mul_gaussH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:16:49.020205+00:00
-- url     : https://prove2.me/theorems/22b61031-bc5c-4ce9-b8f2-be76bb9b6f00
-- title:
--   The Lean 4 theorem `deriv_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deriv_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.deriv_poly_mul_gaussH
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.deriv_poly_mul_gaussH (p : Polynomial ℝ) :
    deriv (fun y : ℝ => p.eval y * gaussH y)
      = fun x : ℝ => (derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x := by sorry
