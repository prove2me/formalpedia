-- Prove2me | Theorems.Thm_DROOptimal_Continuous_lemma_4
-- name    : DROOptimal.Continuous.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:37.035975+00:00
-- url     : https://prove2.me/theorems/ae3171dd-e855-427d-a8fa-24f54d394dbd
-- title:
--   Lemma 4 (35), p. 31 — ĉ_{r,ϵ}(x,ℙ′) ≤ min_{α ≥ γ̄(x)+ϵ} α − e^{−r} exp(∫ log(α − γ) dℙ′), minimizer bound, equality for ϵ > 0
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $\bar\gamma(x)=\max_{\xi\in\Xi}\gamma(x,\xi)$, $c(x,\mathbb P')=\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P'(\xi)$, and let $\hat c_{r,\epsilon}$ be the predictor defined by problem (34).
--
--   **Lemma 4 (Dual representation of $\hat c_{r,\epsilon}$).** Let $r>0$ and $\epsilon\ge0$, and fix $x\in X$, $\mathbb P'\in\mathcal P$. Then:
--
--   1. the problem
--   $$
--   \min_{\alpha\ge\bar\gamma(x)+\epsilon}\ \alpha-e^{-r}\cdot\exp\Big(\int_\Xi\log(\alpha-\gamma(x,\xi))\,\mathrm d\mathbb P'(\xi)\Big)
--   $$
--   has a minimizer $\alpha^\star$ with $\alpha^\star\le\dfrac{\bar\gamma(x)+\epsilon-e^{-r}c(x,\mathbb P')}{1-e^{-r}}$;
--   2. $\hat c_{r,\epsilon}(x,\mathbb P')$ is at most the optimal value of this problem (inequality (35));
--   3. if $\epsilon>0$, then (35) holds with equality.
--
--   The lemma turns the infinite-dimensional problem (34) into a univariate convex program, which is the route to the continuity of $\hat c_r$ (Proposition 6) and to the dual representation (23).
--
--   **Formalization Note** The logarithm follows the convention $\log0=-\infty$; the geometric mean $\exp(\int\log(\alpha-\gamma)\,\mathrm d\mathbb P')$ is defined in the Appendix module as $\inf_{\delta>0}\exp(\int\log(\alpha+\delta-\gamma)\,\mathrm d\mathbb P')$, which equals the paper's value for $\alpha\ge\bar\gamma(x)$ and matters only at $\alpha=\bar\gamma(x)$, $\epsilon=0$. The three claims are stated together for one minimizer $\alpha^\star$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 31, Lemma 4, (35); proof pp. 31–33

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting
import Definitions.Def_DROOptimal_Continuous_Appendix

namespace DROOptimal.Continuous

/-- Lemma 4 (p. 31): for `r > 0`, `ϵ ≥ 0`, the problem `min_{α ≥ γ̄(x)+ϵ} α − e^{−r} exp(∫ log(α − γ) dℙ′)`
has a minimizer `α⋆ ≤ (γ̄(x) + ϵ − e^{−r} c(x, ℙ′)) / (1 − e^{−r})`, its value bounds `ĉ_{r,ϵ}(x, ℙ′)`
from above (35), and (35) is an equality when `ϵ > 0`. -/
theorem lemma_4 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) (x : ↥X) (ℙ' : Dist Ξ) :
    ∃ αstar : ℝ, worstCost γ x + ε ≤ αstar ∧
      αstar ≤ (worstCost γ x + ε - Real.exp (-r) * cost γ x ℙ') / (1 - Real.exp (-r)) ∧
      (∀ α : ℝ, worstCost γ x + ε ≤ α → dualObjective γ r x ℙ' αstar ≤ dualObjective γ r x ℙ' α) ∧
      acPredictor γ r ε x ℙ' ≤ dualObjective γ r x ℙ' αstar ∧
      (0 < ε → acPredictor γ r ε x ℙ' = dualObjective γ r x ℙ' αstar) := by sorry

end DROOptimal.Continuous
