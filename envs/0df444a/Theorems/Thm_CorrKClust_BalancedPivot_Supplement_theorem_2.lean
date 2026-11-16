-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_theorem_2
-- name    : CorrKClust.BalancedPivot.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:48.868375+00:00
-- url     : https://prove2.me/theorems/e2d7a7ec-ecb4-4b5c-9040-e560d97b4754
-- title:
--   Theorem 2 — randomized logarithmic lower bounds
-- statement:
--   There are absolute constants $b,C>0$ and an integer $K\ge2$ such that, for every integer $k\ge K$, put $m=\lceil2\ln k\rceil$ and take the graph $G_k$ formed from $k-1$ cliques of size $m$ and two singletons. Its vertex count $n=(k-1)m+2$ satisfies $k\le n\le Ck\ln k$, and $\operatorname{OPT}_k(G_k)=1$. For every randomized causal online policy,
--   $$\mathbb E[\operatorname{Cost}_{G_k}]\ge b(\ln k)\operatorname{OPT}_k(G_k),\qquad
--   \mathbb E[\operatorname{Cost}_{G_k}]\ge b(\ln n)\operatorname{OPT}_k(G_k).$$
--   The same input precedes every policy, and both inequalities use one uniform positive constant. The expectation includes the uniform order and arbitrary private randomization. No computational restriction is imposed; splitting cliques is permitted. This establishes both claimed competitive lower bounds.
--
--   Differences from the source:
--   - encoding: floor and ceiling rounding omitted in the hard family → clique size ceil(2 ln k) and one sufficiently large integer threshold K; reason: the paper explicitly permits rounding; the strict probability margins survive on every sufficiently large k
--   - encoding: possibly randomized online algorithms in the random-order model → arbitrary real laws on all finite revealed-history policy tables, independent of the order; reason: this represents every private random tape and exposes no future graph or hidden component labels; one smaller absolute b gives both logarithmic conclusions
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Theorem 2, p. 18

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Online

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Theorem 2, printed p.18. The common integer hard instance precedes every policy;
constants are absolute and both the log k and log n conclusions hold on the same graph. -/
theorem theorem_2 :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∃ K : ℕ, 2 ≤ K ∧
    ∀ (k : ℕ) (hk : 0 < k), K ≤ k →
      k ≤ hardN k ∧ (hardN k : ℝ) ≤ C * k * Real.log k ∧
      optK (hardGraph k) k = 1 ∧
      ∀ p : Policy (hardN k) k → ℝ, IsProbWeights p → 
        b * Real.log k * (optK (hardGraph k) k : ℝ) ≤ onlineCost hk (hardGraph k) p ∧
        b * Real.log (hardN k) * (optK (hardGraph k) k : ℝ) ≤ onlineCost hk (hardGraph k) p := by sorry

end CorrKClust.BalancedPivot.Supplement
