-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_scalaronFull1D_mul_gaussPoly
-- name    : BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:31.697199+00:00
-- url     : https://prove2.me/theorems/fbbb61ef-ec30-47aa-8b9e-e3eaa16596a2
-- title:
--   (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) (p : Polynomial ℝ) : MemLp (fun x : ℝ => (((V3.eval x + starobinskyV M alpha x) * gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ)
    (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        (((V3.eval x + starobinskyV M alpha x) * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by sorry
