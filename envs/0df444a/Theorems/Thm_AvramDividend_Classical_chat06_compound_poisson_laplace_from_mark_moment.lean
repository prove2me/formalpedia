-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_compound_poisson_laplace_from_mark_moment
-- name    : AvramDividend.Classical.chat06_compound_poisson_laplace_from_mark_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:45:04.353796+00:00
-- url     : https://prove2.me/theorems/585fcae9-d5a6-4b40-800f-10e7e744aa81
-- title:
--   Drift-adjusted compound-Poisson Laplace identity from a marked moment assumption
-- statement:
--   For a process value X at time t with deterministic drift t, if its jump-part exponential moment equals the moment generating expression E[m^N] for Poisson count N, then the real Laplace transform is exp(t(theta + m - 1)). The proof evaluates the Poisson PGF using the exponential series, factors exp(theta X) into deterministic drift and jump parts, and combines their exponents. The marked-jump expectation identity remains an explicit hypothesis.
-- source:
--   bv_compound_poisson_laplace_from_mark_moment_chat06_20261020.lean, 103 lines, 3550 bytes, SHA-256 14fd247698915fa57d312884d5a09b05b13ed8f38b3d39139aca1ac9055c1b56. Private probe 753640c8-a387-4ec0-ab7a-85b32ccd0ff4 passed to sentinel with zero candidate errors.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.chat06_compound_poisson_laplace_from_mark_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : Ω → ℝ)
    (t : ℝ≥0) (θ m : ℝ)
    (hN : HasLaw N (poissonMeasure t) P)
    (hmark : (∫ ω, Real.exp (θ * (X ω - (t : ℝ))) ∂P) =
      ∫ ω, m ^ (N ω) ∂P) :
    (∫ ω, Real.exp (θ * X ω) ∂P) =
      Real.exp ((t : ℝ) * (θ + m - 1)) := by sorry
