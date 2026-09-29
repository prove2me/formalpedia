-- Prove2me | Theorems.Thm_BookProof_HermiteCore_integrable_poly_mul_gaussH
-- name    : BookProof.HermiteCore.integrable_poly_mul_gaussH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:27:37.486953+00:00
-- url     : https://prove2.me/theorems/9a156880-6c2f-4fb3-a2e7-52a1f181f419
-- title:
--   The Lean 4 theorem `integrable_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integrable_poly_mul_gaussH` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.integrable_poly_mul_gaussH
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.integrable_poly_mul_gaussH (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x * gaussH x) := by sorry
