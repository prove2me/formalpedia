-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integral_gaussPoly_mul
-- name    : BookProof.QgHermiteCore.integral_gaussPoly_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:31:03.887787+00:00
-- url     : https://prove2.me/theorems/6eacc88f-53c1-40de-a869-362041963c48
-- title:
--   (p q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly p x * gaussPoly q x = gint (p * q)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integral_gaussPoly_mul` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integral_gaussPoly_mul
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integral_gaussPoly_mul (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * gaussPoly q x = gint (p * q) := by sorry
