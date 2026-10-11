-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_smooth_on_domain
-- name    : BlackScholesModel.callPrice_smooth_on_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:43:58.990484+00:00
-- url     : https://prove2.me/theorems/2b5c8202-bbc3-4110-9f01-59976aaa9e64
-- title:
--   Smoothness of the Black–Scholes call on the pricing domain
-- statement:
--   For positive strike and volatility, the standard Black–Scholes call price is infinitely continuously differentiable in spot and time on the open pricing domain S>0 and t<T. This is the exact first conjunct of the parent PDE-and-boundary theorem, isolated to support analytic composition of the normal CDF, logarithm, square root and exponential.
-- source:
--   Source-faithful analytic decomposition of BlackScholesModel.callPrice_solves_black_scholes_equation, theorem UUID 7b9f86c4-ef67-48b5-a89c-e0f23038fec0, in the mission Black–Scholes Model: Pricing Formula, PDE and Greeks. Based on the Black–Scholes formula and equation together with its boundary and payoff conditions (Black and Scholes, 1973; published source cited by parent). Each child exactly preserves a separate clause of the parent with the same assumptions and quantifiers.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_smooth_on_domain (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => callPrice K r σ T p.1 p.2)
        {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < T} := by
  sorry

end BlackScholesModel
