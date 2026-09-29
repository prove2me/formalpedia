-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_scalaronHamiltonian_gaussPoly
-- name    : BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:18:44.395434+00:00
-- url     : https://prove2.me/theorems/c7b5e157-3c44-40ad-869e-031ecd43116a
-- title:
--   (M alpha : ℝ) (hM : 0 < M) (p : Polynomial ℝ) : MemLp (fun x : ℝ => ((-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly (M alpha : ℝ) (hM : 0 < M) (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        ((-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by sorry
