-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_greedy_punishing_meets_quotas
-- name    : CompetitivePaging.Combining.greedy_punishing_meets_quotas
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:23:45.018688+00:00
-- url     : https://prove2.me/theorems/0414d0f0-ae58-4dd1-8a59-227152073c51
-- title:
--   The greedy punishing rule punishes each $B(i)$ at least $\lfloor r/c(i)\rfloor$ times by cost $r$
-- statement:
--   Let $c(1),\dots,c(m)$ be positive reals with
--   $$\sum_{i=1}^m\frac1{c(i)}\le 1 .$$
--   Index the units of cost incurred by an on-line algorithm $A$ by $r=0,1,2,\dots$, and let $\mathrm{PUN}_r(i)$ be the number of times $A$ has punished $B(i)$ by the time it has incurred cost $r$, with $\mathrm{PUN}_0(i)=0$. When $A$ incurs its $(r+1)$-st unit of cost it punishes an algorithm $i_{r+1}$ chosen greedily: $i_{r+1}$ minimizes $c(i)\,(\mathrm{PUN}_r(i)+1)$ over all $i$, ties broken arbitrarily. The count of $i_{r+1}$ then grows by at least one, $\mathrm{PUN}_{r+1}(i_{r+1})\ge\mathrm{PUN}_r(i_{r+1})+1$, and no count ever decreases (other algorithms may be punished incidentally). Then for every positive integer $r$ and every $i$,
--   $$\mathrm{PUN}_r(i)\ge\left\lfloor\frac{r}{c(i)}\right\rfloor .$$
--
--   This is the scheduling claim that completes the sufficiency proof of Theorem 6: once $A$ has incurred cost $r$, algorithm $B(i)$ has been punished at least $\lfloor r/c(i)\rfloor$ times.
--
--   **Formalization Note** The choice sequence is indexed from $0$: `choice r` is $i_{r+1}$ and `pun r i` is $\mathrm{PUN}_r(i)$. The counts are an arbitrary function subject to `pun 0 i = 0` and `pun r i + [choice r = i] ≤ pun (r+1) i`, so punishments of algorithms other than the chosen one are allowed, as in the paper, where $\mathrm{PUN}$ counts every punishment. The floor is `Nat.floor` of a real number. For $m=0$ no choice sequence exists and the statement is vacuous, as is the paper's.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 9 (PDF p. 10), §6, proof of Theorem 6 (sufficiency), last paragraph

import Mathlib

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6, p. 9, the scheduling claim. Index `A`'s units of
cost by `r = 0, 1, 2, …` (a lazy `A` pays one unit per fault). `pun r i` is `PUN(i, ·, σ)`, the
number of times `A` has punished `B(i)` by the time it has incurred cost `r`; it starts at `0`.
At its `(r+1)`-st unit of cost `A` punishes `choice r`, the `B(i)` for which
`c(i) · (PUN(i) + 1)` is least (ties broken arbitrarily); the chosen count grows by at least one,
and any count may also grow by incidental punishments. If every `c(i) > 0` and `∑ 1/c(i) ≤ 1`,
then for all positive integers `r` and all `i`, `B(i)` has been punished at least `⌊r / c(i)⌋`
times by the time `A` incurs cost `r`. -/
theorem greedy_punishing_meets_quotas {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, 1 / c i ≤ 1) (choice : ℕ → Fin m) (pun : ℕ → Fin m → ℕ)
    (hpun0 : ∀ i, pun 0 i = 0)
    (hpun : ∀ (r : ℕ) (i : Fin m), pun r i + (if choice r = i then 1 else 0) ≤ pun (r + 1) i)
    (hgreedy : ∀ (r : ℕ) (j : Fin m),
      c (choice r) * ((pun r (choice r) : ℝ) + 1) ≤ c j * ((pun r j : ℝ) + 1)) :
    ∀ r : ℕ, 0 < r → ∀ i : Fin m, ⌊(r : ℝ) / c i⌋₊ ≤ pun r i := by sorry

end CompetitivePaging.Combining
