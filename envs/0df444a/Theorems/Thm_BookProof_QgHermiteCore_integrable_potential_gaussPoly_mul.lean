-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integrable_potential_gaussPoly_mul
-- name    : BookProof.QgHermiteCore.integrable_potential_gaussPoly_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:26:45.820214+00:00
-- url     : https://prove2.me/theorems/bd144778-313b-4482-baf2-69cbbc0f33db
-- title:
--   {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W) (p q : Polynomial ℝ) : Integrable (fun x : ℝ => W x * (gaussPoly p x * gaussPoly q x))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integrable_potential_gaussPoly_mul` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integrable_potential_gaussPoly_mul
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integrable_potential_gaussPoly_mul {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ExpBounded W) (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => W x * (gaussPoly p x * gaussPoly q x)) := by sorry
