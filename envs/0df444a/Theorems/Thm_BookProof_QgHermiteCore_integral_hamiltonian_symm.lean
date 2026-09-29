-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integral_hamiltonian_symm
-- name    : BookProof.QgHermiteCore.integral_hamiltonian_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:18:38.019978+00:00
-- url     : https://prove2.me/theorems/0e0c4265-5f40-418c-9045-01bc05e671b0
-- title:
--   {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W) (p q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x) = ∫ x : ℝ, (-deriv...
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integral_hamiltonian_symm` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integral_hamiltonian_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integral_hamiltonian_symm {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x) * gaussPoly q x := by sorry
