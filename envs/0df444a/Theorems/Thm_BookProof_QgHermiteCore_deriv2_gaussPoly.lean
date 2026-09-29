-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_deriv2_gaussPoly
-- name    : BookProof.QgHermiteCore.deriv2_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:28:39.850543+00:00
-- url     : https://prove2.me/theorems/58750426-1a93-4625-b1e5-545323693f8c
-- title:
--   (p : Polynomial ℝ) : deriv (deriv (gaussPoly p)) = gaussPoly (gaussPolyDeriv (gaussPolyDeriv p))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.deriv2_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.deriv2_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.deriv2_gaussPoly (p : Polynomial ℝ) :
    deriv (deriv (gaussPoly p)) = gaussPoly (gaussPolyDeriv (gaussPolyDeriv p)) := by sorry
