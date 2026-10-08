-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_best_response_monotone_lipschitz
-- name    : DemandSubstitution.Competitive.best_response_monotone_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:29.02899+00:00
-- url     : https://prove2.me/theorems/2920e7bc-d78e-4486-9e18-06ab1b14c6e1
-- title:
--   Proof of Proposition 4, p. 9 — Br_i(Q_{−i}) is monotonic with slope between 0 and a_ji in absolute value
-- statement:
--   Consider the competitive substitution game with a demand law that is a probability law on $\mathbb R^n$ with positive support, integrable coordinates, and a Lebesgue density that is strictly positive on the open positive orthant. Fix a product $i$, two nonnegative stock vectors $Q$ and $Q'$, and let $q$ and $q'$ be best responses of firm $i$ to $Q_{-i}$ and to $Q'_{-i}$ respectively. Then:
--
--   1. (slope bound)
--   $$
--   |q-q'| \le \sum_{j\ne i} a_{ji}\,|Q_j-Q'_j| ;
--   $$
--   2. (monotonicity) if $Q_j\le Q'_j$ for every $j$, then $q'\le q$: firm $i$'s best response does not increase when its rivals stock more.
--
--   Here $a_{ji}$ is the fraction of product $j$'s unmet demand that switches to product $i$. These two facts are the paper's statement that $Br_i$ is monotonic with slope between $0$ and $a_{ji}$ in absolute value; they bound the entries of the Jacobian of the best-response map.
--
--   **Formalization Note** The paper's slope bound is about the partial derivatives $\partial Br_i/\partial Q_j$, computed with a density of $D^s_i$ that the model does not supply. The statement here is the difference (Lipschitz) form, which needs no differentiability of $Br_i$. The positive-density hypothesis is the same disclosed pin as for single-valued best responses.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 9, proof of Proposition 4, sentence after the Jacobian display

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), proof of Proposition 4, p. 9: the best response
`Br_i(Q_{-i})` is monotonic (nonincreasing) and its slope in `Q_j` is between `0` and `a_ji`
in absolute value, stated in difference form. -/
theorem best_response_monotone_lipschitz {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ)
    (Q Q' : Fin n → ℝ) (hQ : ∀ j, 0 ≤ Q j) (hQ' : ∀ j, 0 ≤ Q' j) (i : Fin n) (q q' : ℝ)
    (hq : IsBestResponse M μ Q i q) (hq' : IsBestResponse M μ Q' i q') :
    |q - q'| ≤ ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| ∧
      ((∀ j, Q j ≤ Q' j) → q' ≤ q) := by sorry

end DemandSubstitution.Competitive
