-- Prove2me | Theorems.Thm_BalancedKneser_theorem_1_2
-- name    : BalancedKneser.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:20.771331+00:00
-- url     : https://prove2.me/theorems/07e330a5-b303-4fce-afd3-606d743140a9
-- title:
--   Theorem 1.2 — $\chi(G_{n,2})=6$ for $n\ge2$, and $10\le\chi(G_{n,3})\le14$ for $n\ge4$ with $\chi(G_{4,3})=14$
-- statement:
--   Let $G_{n,r}=KG(2n,n,r)$ be the graph on the $n$-subsets of $[2n]$ in which two distinct sets are adjacent when they share fewer than $r$ elements. Then:
--
--   1. for every $n\ge2$, $\chi(G_{n,2})=6$;
--   2. for every $n\ge4$, $10\le\chi(G_{n,3})\le14$;
--   3. $\chi(G_{4,3})=14$.
--
--   The first equality is the conjecture of Jafari and Alipour (2017); the bound $10$ raises the previous lower bound six of Daneshpajouh, and $14$ is the Fano-plane upper bound of Balogh, Cherkashin and Kiselev. Through Theorem 2.1 these are the balanced EF1 and EF2 thresholds of Theorem 1.1.
--
--   **Formalization Note** $\chi$ is `SimpleGraph.chromaticNumber`, valued in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: χ(G_{n,r}), a natural number → SimpleGraph.chromaticNumber : ℕ∞; reason: the graphs are finite, so χ is finite; same equalities and inequalities
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 1.2, p.1 (PDF p.3); proofs §3.4, p.8 (PDF p.10) and §4.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_BalancedKneser_KG

namespace BalancedKneser

/-- **Theorem 1.2** (Alipour–Jafari, arXiv:2611.04486v1, p.1 (PDF p.3); proofs §3.4, p.8 and
§4.1, p.9): "For every n ≥ 2, χ(G_{n,2}) = 6. For every n ≥ 4, 10 ≤ χ(G_{n,3}) ≤ 14. In the
second statement, equality to fourteen holds when n = 4."

`G_{n,r} = KG(2n, n, r)`: the `n`-subsets of `[2n]`, two distinct ones adjacent when they share
fewer than `r` elements.

Formalization Note: `χ` is `SimpleGraph.chromaticNumber : ℕ∞`. -/
theorem theorem_1_2 :
    (∀ n : ℕ, 2 ≤ n → (Gnr n 2).chromaticNumber = 6) ∧
    (∀ n : ℕ, 4 ≤ n → 10 ≤ (Gnr n 3).chromaticNumber ∧ (Gnr n 3).chromaticNumber ≤ 14) ∧
    (Gnr 4 3).chromaticNumber = 14 := by sorry

end BalancedKneser
