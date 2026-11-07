-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_5_1
-- name    : BilateralOptRegret.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:36.148612+00:00
-- url     : https://prove2.me/theorems/77d9da1b-76c2-4d62-89df-372e9562b25b
-- title:
--   Lemma 5.1 (corrected: $K\ge3$) — the canonical dyadic decomposition
-- statement:
--   Let $K=2^n+1$ with $n\ge1$. For $i'<i$ in $\{0,\dots,K-1\}$, the greedy chain $\mathcal B(i,i')\subseteq\mathcal I^\star$ satisfies
--   $$\sum_{(a,b)\in\mathcal B(i,i')}(b-a)=i-i',\qquad|\mathcal B(i,i')|\le2\log_2(K-1).$$
--   It is a consecutive chain from $i'$ to $i$, and the intervals $(a,b]$ of its pairs form a partition of $(i',i]$. In particular, for every row $j$,
--   $$F(x_{i,j})-F(x_{i',j})=\sum_{(a,b)\in\mathcal B(i,i')}\big(F(x_{b,j})-F(x_{a,j})\big).$$
--   This lets any same-row CDF difference be rebuilt from $O(K)$ elementary differences.
--
--   Differences from the source:
--   - correction: all $K\ge2$ with $K-1$ a power of two → $n\ge1$, i.e. $K\ge3$; reason: the printed lemma is false at $K=2$, which §2.2 admits: by (9) $\mathcal I^\star=\emptyset$, while $i'=0$, $i=1$ needs $\sum(b-a)=1$
--   - encoding: a set $\mathcal B(i,i')$ → a list in chain order; reason: the chain order is the one App. B constructs, and Lemmas 7.2, 7.3 use it
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 5.1, p.18 (proof App. B, pp.43–44)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Dyadic

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 5.1** (corrected: `K ≥ 3`), Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.18; proof App. B, pp.43–44: the canonical dyadic decomposition.

For `K = 2^n + 1`, `n ≥ 1`, and `i′ < i`, the greedy chain `B(i, i′)` lies in `I⋆`, is a consecutive chain from `i′` to `i`, has
`∑ (b − a) = i − i′` and `|B(i, i′)| ≤ 2 log₂(K − 1)`, and its intervals partition `(i′, i]`. Consequently, on every row `j`,
`F(x_{i,j}) − F(x_{i′,j}) = ∑_{(a,b) ∈ B(i,i′)} (F(x_{b,j}) − F(x_{a,j}))` (p.18).

**Formalization Note.** The printed lemma fails at `K = 2`, which §2.2 admits: there `I⋆ = ∅` by (9), while `i′ = 0`, `i = 1`
needs a decomposition with sum `1`. Hence `n ≥ 1`. -/
theorem lemma_5_1 (n : ℕ) (hn : 1 ≤ n) (i' i : Idx n) (hi : i' < i) :
    (∀ p ∈ B n i i', p ∈ Istar n) ∧
    ((B n i i').map fun p => p.2.val - p.1.val).sum = i.val - i'.val ∧
    ((B n i i').length : ℝ) ≤ 2 * Real.logb 2 ((Kof n : ℝ) - 1) ∧
    List.IsChain (fun p q => p.2 = q.1) (B n i i') ∧
    (B n i i').head?.map Prod.fst = some i' ∧
    (B n i i').getLast?.map Prod.snd = some i ∧
    (B n i i').Pairwise (fun p q => Disjoint (Finset.Ioc p.1 p.2) (Finset.Ioc q.1 q.2)) ∧
    (∀ u : Idx n, (i' < u ∧ u ≤ i) ↔ ∃ p ∈ B n i i', p.1 < u ∧ u ≤ p.2) ∧
    ∀ (L : Measure (ℝ × ℝ)) (j : Idx n),
      F L (pt (Kof n) (i, j)) - F L (pt (Kof n) (i', j)) =
        ((B n i i').map fun p => F L (pt (Kof n) (p.2, j)) - F L (pt (Kof n) (p.1, j))).sum := by sorry

end BilateralOptRegret
