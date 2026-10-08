-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_firm_profit_concave
-- name    : DemandSubstitution.Competitive.firm_profit_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:25.222437+00:00
-- url     : https://prove2.me/theorems/f86150c6-f04e-4ea5-8a50-9bd02c86b78b
-- title:
--   §2.2, p. 8 — given Q_{−i}, firm i's expected profit π_i is concave in Q_i
-- statement:
--   In the competitive substitution model, fix product $i$ and nonnegative stocks $Q_{-i}$ of the other products. Assume the demand law is a probability law, absolutely continuous on $\mathbb R^n$, with positive support and integrable coordinates. Then firm $i$'s expected profit (9)
--   $$
--   Q_i \longmapsto \pi_i(Q_i, Q_{-i}) = E\big[u_iD^s_i - u_i(D^s_i-Q_i)^+ - o_i(Q_i-D^s_i)^+\big]
--   $$
--   is concave on the strategy space $Q_i\ge 0$.
--
--   Concavity makes every stationary point of $\pi_i(\cdot,Q_{-i})$ a best response, which is how the first-order condition (10) characterizes the competitive equilibrium.
--
--   **Formalization Note** Concavity is stated on $[0,\infty)$, the set of stocking quantities.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 8, §2.2, sentence before the derivative display

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), §2.2, p. 8: given `Q_{-i}`, `π_i` is concave in `Q_i`
on the strategy space `Q_i ≥ 0`. -/
theorem firm_profit_concave {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (hQ : ∀ j, 0 ≤ Q j)
    (i : Fin n) :
    ConcaveOn ℝ (Set.Ici 0) (fun q : ℝ => firmProfit M μ (Function.update Q i q) i) := by sorry

end DemandSubstitution.Competitive
