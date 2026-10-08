-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_proposition3_nash_foc
-- name    : DemandSubstitution.Competitive.proposition3_nash_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:20.610416+00:00
-- url     : https://prove2.me/theorems/94b2b548-3bb0-45b8-952c-0881e29b350f
-- title:
--   Proposition 3, p. 8 — Nash equilibria are characterized by Pr(D_i < Q^d_i) − Pr(D_i < Q^d_i < D^s_i) = u_i/(u_i + o_i)
-- statement:
--   Consider the competitive substitution game: firm $i$ chooses a stock $Q_i\ge0$ of product $i$ and earns the expected profit (9), where the effective demand $D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+$ includes the customers substituting from other out-of-stock products. Assume the demand law is a probability law, absolutely continuous on $\mathbb R^n$, with positive support and integrable coordinates.
--
--   A nonnegative stock vector $Q^d$ is a Nash equilibrium if and only if, for every $i=1,\dots,n$,
--   $$
--   \Pr\big(D_i<Q^d_i\big) - \Pr\big(D_i<Q^d_i<D^s_i\big) = \frac{u_i}{u_i+o_i},
--   $$
--   where $D^s_i$ is evaluated at $Q^d$ and $u_i=r_i-c_i$, $o_i=c_i-s_i$.
--
--   The condition (10) is a newsvendor critical-ratio condition, adjusted by the second term for the extra demand of substituting customers. It is the form in which the equilibrium is compared with the centralized solution.
--
--   **Formalization Note** The Nash equilibrium is defined by the absence of a profitable deviation over nonnegative stocks, not by (10); this theorem states that the two are equivalent on nonnegative stock vectors ("characterized by"). The probabilities keep the paper's strict inequalities.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 8, Proposition 3, (10)

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), Proposition 3, p. 8: Nash equilibria are characterized by the
optimality conditions (10): a nonnegative stock vector is a Nash equilibrium if and only if it
satisfies (10) for every product `i`. -/
theorem proposition3_nash_foc {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (hQ : ∀ i, 0 ≤ Q i) :
    IsNash M μ Q ↔ ∀ i, FOC10 M μ Q i := by sorry

end DemandSubstitution.Competitive
