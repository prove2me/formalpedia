-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_hasDerivAt_gaussPoly
-- name    : BookProof.QgHermiteCore.hasDerivAt_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:29:40.653596+00:00
-- url     : https://prove2.me/theorems/20b4e28f-9a47-4d62-9675-d8295284c461
-- title:
--   (p : Polynomial ℝ) (x : ℝ) : HasDerivAt (gaussPoly p) (gaussPoly (gaussPolyDeriv p) x) x
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.hasDerivAt_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.hasDerivAt_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.hasDerivAt_gaussPoly (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussPoly p) (gaussPoly (gaussPolyDeriv p) x) x := by sorry
