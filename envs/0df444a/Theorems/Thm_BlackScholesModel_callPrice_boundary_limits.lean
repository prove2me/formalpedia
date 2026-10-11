-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_boundary_limits
-- name    : BlackScholesModel.callPrice_boundary_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:43:16.504522+00:00
-- url     : https://prove2.me/theorems/58854b69-bba7-4435-8d19-0e28313543e4
-- title:
--   Zero-spot, infinite-spot and expiry limits for the Black–Scholes call
-- statement:
--   Three asymptotic properties of the Black–Scholes call: the price tends to zero at zero spot, its difference from discounted intrinsic forward value tends to zero at infinite spot, and the price approaches the positive-part payoff at expiry from below. These are the exact final three conjuncts of the parent theorem, grouped as its boundary-value problem. The infinite-spot condition needs a Gaussian tail estimate strong enough to offset S.
-- source:
--   Source-faithful analytic decomposition of BlackScholesModel.callPrice_solves_black_scholes_equation, theorem UUID 7b9f86c4-ef67-48b5-a89c-e0f23038fec0, in the mission Black–Scholes Model: Pricing Formula, PDE and Greeks. Based on the Black–Scholes formula and equation together with its boundary and payoff conditions (Black and Scholes, 1973; published source cited by parent). Each child exactly preserves a separate clause of the parent with the same assumptions and quantifiers.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_boundary_limits (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    (∀ t : ℝ, t < T → Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ t : ℝ, t < T →
      Tendsto (fun S => callPrice K r σ T S t - (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0)) ∧
    (∀ S : ℝ, 0 < S →
      Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T) (𝓝 (max (S - K) 0))) := by
  sorry

end BlackScholesModel
