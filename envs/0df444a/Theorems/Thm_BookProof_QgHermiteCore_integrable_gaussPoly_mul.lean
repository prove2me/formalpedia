-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integrable_gaussPoly_mul
-- name    : BookProof.QgHermiteCore.integrable_gaussPoly_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:30:23.27506+00:00
-- url     : https://prove2.me/theorems/5b56ba29-7b48-417e-8a11-466a27f9e65c
-- title:
--   (p q : Polynomial ℝ) : Integrable (fun x : ℝ => gaussPoly p x * gaussPoly q x)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integrable_gaussPoly_mul` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integrable_gaussPoly_mul
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integrable_gaussPoly_mul (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => gaussPoly p x * gaussPoly q x) := by sorry
