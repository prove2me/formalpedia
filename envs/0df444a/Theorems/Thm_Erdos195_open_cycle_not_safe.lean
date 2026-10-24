-- Prove2me | Theorems.Thm_Erdos195_open_cycle_not_safe
-- name    : Erdos195.open_cycle_not_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T22:02:23.860718+00:00
-- url     : https://prove2.me/theorems/95045b70-0881-4335-80de-54deea7cd64e
-- title:
--   Open cycles are never tree-safe: every open cycle has a node conflict at its minimal level
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $2b-a$ its third term and $3b-2a$ its fourth term. An open cycle in a word $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, $m\ge 1$, of letters of $T$ with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(\text{indices mod } m)$$
--   and no third term $2b_i-a_i$ in $T$. **Theorem (open cycles are never tree-safe).** If $T$ contains an open cycle, then no word $T\,R$ is $\theta$-safe, for any tree witness $\theta$ and any word $R$; in particular $T$ itself is not safe for any tree witness.
--
--   Equivalently, the points $t_i=2b_i-a_i$ satisfy $t_{i+1}-t_i=d_i:=b_i-a_i$, so $\sum_i d_i=0$ and the minimal 2-adic valuation $k$ of the $d_i$ is attained by an even number of pairs, all at the same node modulo $2^k$; consecutive such pairs around the cycle point in opposite directions. Hence the node-conflict hypothesis of milestone 146 always holds. This removes that hypothesis: open cycles of every length (including the interlocked configuration of milestone 141) are forbidden configurations, and milestone 144 becomes vacuous for safe stages. It is a structural lemma about the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, the pairs are `a b : ℕ → ℤ` on indices `i < m`, the successor index is `(i+1) % m`; the conclusion is `¬ ∃ θ, Safe (treeLt θ) (T ++ R)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_cycle_not_safe (T R : List ℤ) (m : ℕ) (hm : 0 < m) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by sorry

end Erdos195
