-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_abs_poly_mul_exp_neg_eighth
-- name    : BookProof.QgHermiteCore.memLp_abs_poly_mul_exp_neg_eighth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:31:41.411743+00:00
-- url     : https://prove2.me/theorems/b103fc53-0e49-4ae0-95ad-597cf64d382c
-- title:
--   (p : Polynomial ℝ) : MemLp (fun x : ℝ => ((|p.eval x| * Real.exp (-x ^ 2 / 8) : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_abs_poly_mul_exp_neg_eighth` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_abs_poly_mul_exp_neg_eighth
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_abs_poly_mul_exp_neg_eighth (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((|p.eval x| * Real.exp (-x ^ 2 / 8) : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by sorry
