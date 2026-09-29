-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_gaussPoly
-- name    : BookProof.QgHermiteCore.memLp_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:32:25.715103+00:00
-- url     : https://prove2.me/theorems/886fed94-7d3a-4763-a0c1-691f459c595a
-- title:
--   (p : Polynomial ℝ) : MemLp (fun x : ℝ => ((gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_gaussPoly (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by sorry
