-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_hamiltonian_gaussPoly
-- name    : BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:50.264931+00:00
-- url     : https://prove2.me/theorems/edec04b2-8db5-4f47-9c3e-0a096931ea5b
-- title:
--   {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W) (p : Polynomial ℝ) : MemLp (fun x : ℝ => ((-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        ((-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by sorry
