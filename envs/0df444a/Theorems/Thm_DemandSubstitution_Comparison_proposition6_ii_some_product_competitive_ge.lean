-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_proposition6_ii_some_product_competitive_ge
-- name    : DemandSubstitution.Comparison.proposition6_ii_some_product_competitive_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:43.546233+00:00
-- url     : https://prove2.me/theorems/d63893b2-1a56-45b7-9690-0416207e990e
-- title:
--   Proposition 6(ii), p. 10 — for every centralized optimum Q^c and Nash equilibrium Q^d, Q^c_i ≤ Q^d_i for at least one i
-- statement:
--   Consider the $n$-product substitution model with $n \ge 1$ products and a demand law $\mu$ that has a Lebesgue density strictly positive on the open positive orthant. Let $Q^c$ be any optimal centralized stocking vector (a nonnegative maximizer of the centralized expected profit) and $Q^d$ any Nash equilibrium of the game in which firm $i$ chooses $Q_i \ge 0$ to maximize its own expected profit (9). Then
--   $$\exists\, i \in \{1,\dots,n\}:\qquad Q^c_i \le Q^d_i .$$
--
--   In words, competition never leads to understocking of every product relative to centralized management: at least one product is stocked no less under competition. The paper contrasts this with Proposition 6(i), that some product may be stocked more under centralization, against the common view that competition leads to overstocking of all products.
--
--   **Formalization Note** Two hypotheses are disclosed pins. $n \ge 1$ (`NeZero n`) excludes the empty product set, for which "at least one $i$" fails. The positive density makes the distribution functions of $D^s_i$ strictly increasing, which the paper's last step ("This, however, implies that $Q^c_i \le Q^d_i$ for an inequality to hold") uses without stating it. No interiority is assumed: the statement covers every optimum and every equilibrium, including ones with zero components.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 10, Proposition 6(ii); proof pp. 10–11

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Proposition 6(ii), p. 10: for every optimal centralized stocking vector `Q^c` and every Nash
equilibrium `Q^d` of the competitive game, `Q^c_i ≤ Q^d_i` for at least one product `i`.
`[NeZero n]` (at least one product) and `HasPositiveDensity μ` are disclosed pins. -/
theorem proposition6_ii_some_product_competitive_ge {n : ℕ} [NeZero n] (M : Model n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ)
    (hf : DemandSubstitution.Competitive.HasPositiveDensity μ) (Qc Qd : Fin n → ℝ)
    (hc : IsCentralOptimal M μ Qc) (hd : IsNash M μ Qd) :
    ∃ i, Qc i ≤ Qd i := by sorry

end DemandSubstitution.Comparison
