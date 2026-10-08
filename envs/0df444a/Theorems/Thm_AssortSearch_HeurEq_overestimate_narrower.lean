-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_overestimate_narrower
-- name    : AssortSearch.HeurEq.overestimate_narrower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:15.862637+00:00
-- url     : https://prove2.me/theorems/c210b3dc-b5d0-4b43-a9ed-98317d32e0ea
-- title:
--   At a heuristic equilibrium the retailer over-estimates the profit of every narrower assortment
-- statement:
--   Under the hypotheses of the mission ($v_1\ge\dots\ge v_n>0$, $v_0>0$, $\lambda>0$, monotone margins $m_j\ge m_k$ whenever $v_j\ge v_k$, $c$ concave and increasing on $[0,1]$ with $c(0)\ge0$), let $x^*$ be a heuristic equilibrium of iterative no-search assortment planning in the independent assortment model. Then for every assortment narrower than $x^*$,
--   $$\pi(x)\ \le\ \pi(x\mid\hat v(x^*))\qquad(1\le x<x^*),$$
--   where $\pi(x)$ is the true expected profit and $\pi(x\mid\hat v(x^*))$ the profit the no-search model predicts with the estimates $\hat v(x^*)$.
--
--   This combines Theorem 7 with the non-negativity of estimated variant profits, and is the comparison on which the proof of Theorem 8 rests.
--
--   **Formalization Note** $c(0)\ge0$ is added as in the positivity milestone. The per-variant version $\pi_i(x)\le\pi_i(x\mid\hat v(x^*))$ is implied and not posed separately.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 23–24 (PDF 25–26), proof of Theorem 8, π(x) ≤ π(x|v̂(x*)) for 1 ≤ x < x*

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Proof of Theorem 8, pp. 23–24: at a heuristic equilibrium `x*` the retailer over-estimates
the expected profit of every assortment narrower than `x*`:
`π(x) ≤ π(x | v̂(x*))` for `1 ≤ x < x*`. -/
theorem overestimate_narrower {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x < xstar) :
    trueProfit lam m c v v0 x ≤
      estProfit m c (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar) x := by sorry

end AssortSearch.HeurEq
