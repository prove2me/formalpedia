-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_gaussPoly_of_expBounded
-- name    : BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:27:27.512569+00:00
-- url     : https://prove2.me/theorems/de9d99d1-dcde-4efe-86a3-95ff8447ac05
-- title:
--   {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W) (p : Polynomial ℝ) : MemLp (fun x : ℝ => ((W x * gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ExpBounded W) (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((W x * gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by sorry
