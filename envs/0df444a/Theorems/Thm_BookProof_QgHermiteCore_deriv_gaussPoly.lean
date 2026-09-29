-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_deriv_gaussPoly
-- name    : BookProof.QgHermiteCore.deriv_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:47:42.019894+00:00
-- url     : https://prove2.me/theorems/f723b28d-3ad7-4cd0-82c7-0c9f12b00fe7
-- title:
--   (p : Polynomial ℝ) : deriv (gaussPoly p) = gaussPoly (gaussPolyDeriv p)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.deriv_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.deriv_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.deriv_gaussPoly (p : Polynomial ℝ) :
    deriv (gaussPoly p) = gaussPoly (gaussPolyDeriv p) := by sorry
