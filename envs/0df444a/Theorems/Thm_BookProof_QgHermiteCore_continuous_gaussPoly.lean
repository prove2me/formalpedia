-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_continuous_gaussPoly
-- name    : BookProof.QgHermiteCore.continuous_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:20:41.343772+00:00
-- url     : https://prove2.me/theorems/5bfa60fc-5d21-4bf4-ad8e-ec1492ca1f6b
-- title:
--   (p : Polynomial ℝ) : Continuous (gaussPoly p)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.continuous_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.continuous_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.continuous_gaussPoly (p : Polynomial ℝ) : Continuous (gaussPoly p) := by sorry
