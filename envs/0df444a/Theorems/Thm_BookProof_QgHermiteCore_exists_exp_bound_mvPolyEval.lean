-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_exists_exp_bound_mvPolyEval
-- name    : BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:21:54.804125+00:00
-- url     : https://prove2.me/theorems/3d3e65f5-afdd-4350-96f0-b9fac054cf95
-- title:
--   (p : MvPolynomial (Fin d) ℂ) : ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x : Vd d, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ≤ C * Real.exp (c * ‖x‖)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval (p : MvPolynomial (Fin d) ℂ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x : Vd d,
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ≤ C * Real.exp (c * ‖x‖) := by sorry
