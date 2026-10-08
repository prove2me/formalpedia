-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_proposition4_nash_exists_unique_stable
-- name    : DemandSubstitution.Competitive.proposition4_nash_exists_unique_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:28.199851+00:00
-- url     : https://prove2.me/theorems/19701dd7-9c40-4c1e-899c-901e9588ac5d
-- title:
--   Proposition 4, p. 9 — a Nash equilibrium exists and solves (10); if Σ_i a_ij < 1 ∀j or Σ_j a_ij < 1 ∀i it is unique and globally stable
-- statement:
--   Consider the competitive inventory game with demand substitution: $n$ firms, firm $i$ chooses a stock $Q_i\ge0$ of product $i$ (price $r_i$, cost $c_i$, salvage value $s_i$, $r_i>c_i>s_i>0$) and earns the expected profit
--   $$
--   \pi_i = E\big[u_iD^s_i - u_i(D^s_i-Q_i)^+ - o_i(Q_i-D^s_i)^+\big],\qquad D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+,
--   $$
--   with $u_i=r_i-c_i$, $o_i=c_i-s_i$, substitution fractions $a_{ij}\in[0,1]$, $a_{ii}=0$, $\sum_j a_{ij}<1$. The demand vector $D$ has a probability law on $\mathbb R^n$ with integrable coordinates and a Lebesgue density that is strictly positive on the open positive orthant and vanishes elsewhere almost everywhere (positive support). Then:
--
--   1. A Nash equilibrium exists.
--   2. A nonnegative stock vector $Q$ is a Nash equilibrium if and only if it solves the first-order conditions (10):
--   $$
--   \Pr(D_i<Q_i) - \Pr(D_i<Q_i<D^s_i) = \frac{u_i}{u_i+o_i},\qquad i=1,\dots,n .
--   $$
--   3. If either $\sum_{i=1}^n a_{ij}<1$ for all $j$, or $\sum_{j=1}^n a_{ij}<1$ for all $i$, the Nash equilibrium $Q^d$ is unique and globally stable: every sequence of simultaneous best responses $Q^{(0)},Q^{(1)},\dots$, started at any nonnegative $Q^{(0)}$ (each $Q^{(k+1)}_i$ a best response of firm $i$ to $Q^{(k)}_{-i}$), converges to $Q^d$.
--
--   The result extends earlier uniqueness results for two products and for symmetric problems to an arbitrary number of products with a general demand distribution, and (10) is the expression in which the competitive and the centralized stocking levels are compared.
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based). "Can be found from the first order conditions (10)" is formalized as the equivalence in part 2. "Globally stable" is convergence of every best-response sequence from every nonnegative start; best responses are not defined by a choice function. The second branch of the condition in part 3, $\sum_j a_{ij}<1$ for all $i$, is the paper's own standing assumption of §2, so under the model part 3 always applies; the disjunction is kept as printed. The positive density is a disclosed hypothesis beyond the page: the paper's proof asserts single-valued best responses and divides by the density of $D^s_i$, which needs a strictly increasing distribution function of $D^s_i$.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 9, Proposition 4 and its proof; (10) on p. 8

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), Proposition 4, p. 9: a Nash equilibrium exists and the
equilibria are exactly the nonnegative solutions of (10); if either `∑_i a_ij < 1` for all `j`
or `∑_j a_ij < 1` for all `i`, the equilibrium is unique and globally stable (every sequence of
simultaneous best responses from any nonnegative start converges to it). -/
theorem proposition4_nash_exists_unique_stable {n : ℕ} (M : Model n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ)
    (hf : HasPositiveDensity μ) :
    (∃ Q, IsNash M μ Q) ∧
      (∀ Q : Fin n → ℝ, (∀ i, 0 ≤ Q i) → (IsNash M μ Q ↔ ∀ i, FOC10 M μ Q i)) ∧
      (((∀ j, ∑ i, M.a i j < 1) ∨ (∀ i, ∑ j, M.a i j < 1)) →
        ∃ Qd : Fin n → ℝ, IsNash M μ Qd ∧ (∀ Q, IsNash M μ Q → Q = Qd) ∧
          ∀ seq : ℕ → Fin n → ℝ, (∀ i, 0 ≤ seq 0 i) →
            (∀ k i, IsBestResponse M μ (seq k) i (seq (k + 1) i)) →
            Filter.Tendsto seq Filter.atTop (nhds Qd)) := by sorry

end DemandSubstitution.Competitive
