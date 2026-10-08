-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_best_response_contraction
-- name    : DemandSubstitution.Competitive.best_response_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:23.325074+00:00
-- url     : https://prove2.me/theorems/9793b453-084e-42fa-acf2-0a1989d12b4b
-- title:
--   Proof of Proposition 4, p. 9 — the best-response map is Lipschitz with constant max_j Σ_i a_ji (one-norm) and max_i Σ_j a_ji (infinity-norm)
-- statement:
--   Consider the competitive substitution game with a demand law that is a probability law on $\mathbb R^n$ with positive support, integrable coordinates, and a Lebesgue density that is strictly positive on the open positive orthant. Let $Q,Q'$ be nonnegative stock vectors and let $q,q'$ be profiles of best responses: $q_i$ is a best response of firm $i$ to $Q_{-i}$, and $q'_i$ to $Q'_{-i}$, for every $i$.
--
--   1. (one-norm) If $L$ satisfies $\sum_{i=1}^n a_{ji}\le L$ for every $j$, then
--   $$
--   \sum_{i=1}^n |q_i-q'_i| \le L\sum_{j=1}^n |Q_j-Q'_j| .
--   $$
--   2. (infinity-norm) If $L$ satisfies $\sum_{j=1}^n a_{ji}\le L$ for every $i$, and $|Q_j-Q'_j|\le K$ for every $j$, then $|q_i-q'_i|\le LK$ for every $i$.
--
--   In the paper's words, the spectral radius of the Jacobian of the best-response map is bounded by $\max_j\sum_i a_{ji}<1$, so the best-response map is a contraction. Part 1 is the printed one-norm bound; part 2 is the infinity-norm case that the paper obtains by transposing the Jacobian.
--
--   **Formalization Note** The Jacobian bound is stated as a Lipschitz bound of the best-response map in the corresponding norm, which needs no differentiability. $a_{ji}$ is the share of $j$'s unmet demand going to $i$. The positive-density hypothesis is the same disclosed pin as for single-valued best responses.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 9, proof of Proposition 4, display ρ(J_Br) ≤ ‖J_Br‖₁ ≤ max_j Σ_i a_ji < 1 and the paragraph on the two matrix norms

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), proof of Proposition 4, p. 9: the simultaneous
best-response map is Lipschitz with constant `max_j ∑_i a_ji` in the one-norm and with
constant `max_i ∑_j a_ji` in the infinity-norm. -/
theorem best_response_contraction {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ)
    (Q Q' : Fin n → ℝ) (hQ : ∀ j, 0 ≤ Q j) (hQ' : ∀ j, 0 ≤ Q' j) (q q' : Fin n → ℝ)
    (hq : ∀ i, IsBestResponse M μ Q i (q i)) (hq' : ∀ i, IsBestResponse M μ Q' i (q' i)) :
    (∀ L : ℝ, (∀ j, ∑ i, M.a j i ≤ L) →
        ∑ i, |q i - q' i| ≤ L * ∑ j, |Q j - Q' j|) ∧
      (∀ L K : ℝ, (∀ i, ∑ j, M.a j i ≤ L) → (∀ j, |Q j - Q' j| ≤ K) →
        ∀ i, |q i - q' i| ≤ L * K) := by sorry

end DemandSubstitution.Competitive
