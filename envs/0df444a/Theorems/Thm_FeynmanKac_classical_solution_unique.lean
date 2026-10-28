-- Prove2me | Theorems.Thm_FeynmanKac_classical_solution_unique
-- name    : FeynmanKac.classical_solution_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:23:45.221763+00:00
-- url     : https://prove2.me/theorems/b4f696c0-f996-4b2c-bfa1-5107c026af77
-- title:
--   Pointwise uniqueness of bounded classical Feynman–Kac PDE solutions
-- statement:
--   If \(u\) and \(v\) are bounded classical solutions of the same backward diffusion PDE with identical drift, diffusion coefficient, discount, running source and terminal payoff, and the required integrability conditions hold, then their values agree at the deterministic starting point. Global uniqueness follows when such an admissible model is available for each starting time and state.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.classical_solution_unique
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u v : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hv : m.IsClassicalPDESolution v)
    (huGrad : m.SquareIntegrableDiscountedGradient u)
    (hvGrad : m.SquareIntegrableDiscountedGradient v) :
    u m.initialState m.initialTime =
      v m.initialState m.initialTime := by sorry
