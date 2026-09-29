-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integral_scalaronHamiltonian_symm
-- name    : BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:18:42.553503+00:00
-- url     : https://prove2.me/theorems/5bfb2ea4-0bdb-4041-951b-29dbdce09a9e
-- title:
--   (M alpha : ℝ) (hM : 0 < M) (p q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + starobinskyV M alpha x * gaussPoly q x) = ∫ x : ℝ, (-deriv (deriv...
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm (M alpha : ℝ) (hM : 0 < M) (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x
        * (-deriv (deriv (gaussPoly q)) x + starobinskyV M alpha x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x)
        * gaussPoly q x := by sorry
