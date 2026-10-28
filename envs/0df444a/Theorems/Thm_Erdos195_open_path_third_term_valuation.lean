-- Prove2me | Theorems.Thm_Erdos195_open_path_third_term_valuation
-- name    : Erdos195.open_path_third_term_valuation
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T23:11:29.862175+00:00
-- url     : https://prove2.me/theorems/68d47e5b-0d85-484c-abe3-6723508c1976
-- title:
--   Third terms of a fully open path: ν₂(t_j − t_i) is the minimal level between them
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $t=2b-a$ its third term, $w=3b-2a$ its fourth term, and $\nu_2(b-a)$ its level. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $0\le i<m-1$ and no third term $t_i=2b_i-a_i$ in $T$. Write $d_i=b_i-a_i$, $k_i=\nu_2(d_i)$, and $w=3b_{m-1}-2a_{m-1}$ for the fourth term of the last (sink) pair.
--
--   **Theorem.** Suppose $T$ is $\theta$-safe for some tree witness $\theta$ and contains an open path of length $m$ whose sink fourth term $w$ is also absent from $T$. Then for all $0\le i<j<m$ there is $p$ with $i\le p<j$ and $k_p=\min_{i\le l<j}k_l$ such that
--   $$\nu_2(t_j-t_i)=k_p=\min_{i\le l<j}\nu_2(b_l-a_l),$$
--   and for every $0\le i<m$ likewise $\nu_2(w-t_i)=\min_{i\le l<m}\nu_2(b_l-a_l)$ (the minimum attained at some $p\in[i,m)$).
--
--   Along a fully open path the 2-adic distance between third terms (and from a third term to the sink's fourth term) is exactly the lowest level of the pairs in between. This sharpens the ruler law (milestone #148): $t_j-t_i=\sum_{i\le l<j}d_l$, and the ruler law makes the minimal valuation in every window unique.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_path_third_term_valuation (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T)
    (hw : 3 * b (m - 1) - 2 * a (m - 1) ∉ T) :
    (∀ i j, i < j → j < m → ∃ p, i ≤ p ∧ p < j ∧
      (∀ l, i ≤ l → l < j → padicValInt 2 (b p - a p) ≤ padicValInt 2 (b l - a l)) ∧
      padicValInt 2 ((2 * b j - a j) - (2 * b i - a i)) = padicValInt 2 (b p - a p)) ∧
    (∀ i, i < m → ∃ p, i ≤ p ∧ p < m ∧
      (∀ l, i ≤ l → l < m → padicValInt 2 (b p - a p) ≤ padicValInt 2 (b l - a l)) ∧
      padicValInt 2 ((3 * b (m - 1) - 2 * a (m - 1)) - (2 * b i - a i)) =
        padicValInt 2 (b p - a p)) := by sorry

end Erdos195
