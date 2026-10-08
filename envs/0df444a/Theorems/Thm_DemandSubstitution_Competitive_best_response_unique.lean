-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_best_response_unique
-- name    : DemandSubstitution.Competitive.best_response_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:22.841778+00:00
-- url     : https://prove2.me/theorems/d1873cdb-106a-4e55-881e-e42e9c6d13a6
-- title:
--   Proof of Proposition 4, p. 9 — each best response is single-valued and is found from the first-order condition (10)
-- statement:
--   Consider the competitive substitution game with a demand law that is a probability law on $\mathbb R^n$ with positive support, integrable coordinates, and a Lebesgue density that is strictly positive on the open positive orthant. Fix a product $i$ and nonnegative stocks $Q$ (only $Q_{-i}$ matters).
--
--   1. Firm $i$ has exactly one best response $q\ge0$ to $Q_{-i}$, i.e. exactly one maximizer of $\pi_i(\cdot,Q_{-i})$ over $[0,\infty)$.
--   2. A stock $q\ge0$ is that best response if and only if it satisfies the first-order condition
--   $$
--   \Pr(D_i<q) - \Pr(D_i<q<D^s_i) = \frac{u_i}{u_i+o_i},\qquad D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+ .
--   $$
--
--   Single-valuedness turns the best-response correspondence into a map $Br_i(Q_{-i})$, which is what the contraction argument for Proposition 4 iterates.
--
--   **Formalization Note** The positive density is a disclosed hypothesis beyond the page: the paper derives single-valuedness from concavity alone and divides by the density of $D^s_i$, but concavity does not exclude a flat stretch of the distribution function of $D^s_i$ (and hence an interval of maximizers). Strict positivity of the density on the positive orthant rules this out.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 9, proof of Proposition 4, first paragraph

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), proof of Proposition 4, p. 9: each best response is
single-valued, and given the other firms' stocks the unique best response is found from the
first-order condition (10). -/
theorem best_response_unique {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ)
    (Q : Fin n → ℝ) (hQ : ∀ j, 0 ≤ Q j) (i : Fin n) :
    (∃! q : ℝ, IsBestResponse M μ Q i q) ∧
      ∀ q : ℝ, 0 ≤ q → (IsBestResponse M μ Q i q ↔ FOC10 M μ (Function.update Q i q) i) := by sorry

end DemandSubstitution.Competitive
