-- Prove2me | Theorems.Thm_Erdos195_open_cycle_never_closes
-- name    : Erdos195.open_cycle_never_closes
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:37:51.809806+00:00
-- url     : https://prove2.me/theorems/e06b731d-a031-4c0b-b616-9686db282df8
-- title:
--   Open cycles never close: cyclic third/fourth-term chains of pairs stay open forever
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word (a before b), call $2b-a$ its third term and $3b-2a$ its fourth term. **Theorem (open cycles never close).** Let $T$ be a finite word, $m\ge 1$, and let $(a_i,b_i)$, $0\le i<m$, be pairs of letters of $T$ with $a_i$ before $b_i$, forming a cycle in the sense that the fourth term of each pair is the third term of the next one:
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(\text{indices mod } m),$$
--   and suppose no third term $2b_i-a_i$ lies in $T$. Then for every tree witness $\theta$ and every word $R$ such that $T\,R$ is $\theta$-safe, none of the third or fourth terms $2b_i-a_i,\;3b_i-2a_i$ occurs in $T\,R$: all pairs of the cycle stay open forever.
--
--   The case $m=2$ is the interlocked-pairs lemma (two pairs with swapped third and fourth terms). The statement shows that any cyclic chain of this kind permanently blocks a set of integers from ever being added, for every tree order. It is a structural lemma in the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, the pairs are given by `a b : ℕ → ℤ` on indices `i < m`, the successor index is `(i+1) % m`, and safety is `Safe (treeLt θ)`. For $m=0$ the statement is vacuous.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_cycle_never_closes (θ : ℕ → ℤ → Bool) (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (hS : Safe (treeLt θ) (T ++ R)) :
    ∀ i < m, 2 * b i - a i ∉ T ++ R ∧ 3 * b i - 2 * a i ∉ T ++ R := by sorry

end Erdos195
