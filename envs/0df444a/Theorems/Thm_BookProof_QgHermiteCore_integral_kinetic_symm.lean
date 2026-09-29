-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_integral_kinetic_symm
-- name    : BookProof.QgHermiteCore.integral_kinetic_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:43.109183+00:00
-- url     : https://prove2.me/theorems/5b6eed02-a1f5-4224-85f6-f9c3d645639a
-- title:
--   (p q : Polynomial ℝ) : ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x) = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.integral_kinetic_symm` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.integral_kinetic_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.integral_kinetic_symm (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x := by sorry
