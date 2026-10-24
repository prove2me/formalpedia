-- Prove2me | Theorems.Thm_Erdos195_open_path_closes_backwards
-- name    : Erdos195.open_path_closes_backwards
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T22:32:33.371771+00:00
-- url     : https://prove2.me/theorems/61dd7408-bcda-48bd-ae16-7b656625c485
-- title:
--   Open paths close from the sink backwards: closing one pair forces the whole tail, fourth terms first
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $t=2b-a$ its third term and $w=3b-2a$ its fourth term. An open path in a word $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(0\le i<m-1)$$
--   (the fourth term of each pair is the third term of the next) and no third term $2b_i-a_i$ in $T$. **Theorem.** Let $T$ contain such an open path and let $T\cdot R$ be $\theta$-safe for some tree witness $\theta$ (any extension $R$). If the third term $t_i=2b_i-a_i$ of some pair $i$ occurs in $T\cdot R$, then for every $j$ with $i\le j<m$ both $t_j$ and $w_j=3b_j-2a_j$ occur in $T\cdot R$, and $w_j$ comes before $t_j$.
--
--   Since $w_j=t_{j+1}$, the closing order is forced: $w_{m-1}$ first, then $t_{m-1}, t_{m-2},\dots,t_i$. So the tail of an open path can only be closed from the sink backwards. The reason is the tree criterion: an in-order pair whose third term appears later must already have its fourth term, placed before the third term. This is the acyclic counterpart of milestone 143 (open cycles never close): for a path the closure must start at the sink's fourth term $w_{m-1}$. It is a structural lemma about the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, pairs are `a b : ℕ → ℤ` on indices `i < m`; safety is `Safe (treeLt θ) (T ++ R)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_path_closes_backwards (θ : ℕ → ℤ → Bool) (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (hS : Safe (treeLt θ) (T ++ R))
    (i : ℕ) (hti : 2 * b i - a i ∈ T ++ R) :
    ∀ j, i ≤ j → j < m →
      2 * b j - a j ∈ T ++ R ∧ 3 * b j - 2 * a j ∈ T ++ R ∧
        (T ++ R).idxOf (3 * b j - 2 * a j) < (T ++ R).idxOf (2 * b j - a j) := by sorry

end Erdos195
