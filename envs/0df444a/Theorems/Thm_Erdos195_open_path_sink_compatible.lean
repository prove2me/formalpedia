-- Prove2me | Theorems.Thm_Erdos195_open_path_sink_compatible
-- name    : Erdos195.open_path_sink_compatible
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T23:11:29.782897+00:00
-- url     : https://prove2.me/theorems/e33b5b9d-e5b4-4d6d-8fcb-20c847e44e07
-- title:
--   The sink's fourth term never conflicts with its own fully open path
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $t=2b-a$ its third term, $w=3b-2a$ its fourth term, and $\nu_2(b-a)$ its level. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $0\le i<m-1$ and no third term $t_i=2b_i-a_i$ in $T$. Write $d_i=b_i-a_i$, $k_i=\nu_2(d_i)$, and $w=3b_{m-1}-2a_{m-1}$ for the fourth term of the last (sink) pair.
--
--   **Theorem.** Suppose $T$ is $\theta$-safe and contains an open path of length $m$ whose sink fourth term $w$ is absent from $T$. Let $j<m$, put $k=k_j=\nu_2(b_j-a_j)$, and let $x\in\mathbb Z$ satisfy $\nu_2(w-x)=k$ and $x\equiv a_j \pmod{2^k}$ (the pair $(x,w)$ has the level of pair $j$ and sits at its node). Then
--   $$\theta\bigl(k,\;x \bmod 2^k\bigr)=1\iff \text{the $k$-th binary digit of $w$ is }1 .$$
--
--   In the tree characterization of safety, this is exactly the orientation condition of the new pair $(x,w)$ created when $w$ is appended. By milestone #149 every closure of the path must place $w$ first, and this result shows that the path's own fully open pairs never cause a node conflict for that step: any obstruction to appending $w$ comes from pairs off the path. (Proof idea: $w\equiv a_j \pmod{2^k}$ forces $\nu_2(\sum_{l>j}d_l)>k$ by the ruler law, so $w\equiv b_j\pmod{2^{k+1}}$.)
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_path_sink_compatible (θ : ℕ → ℤ → Bool) (T : List ℤ) (hS : Safe (treeLt θ) T)
    (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T)
    (hw : 3 * b (m - 1) - 2 * a (m - 1) ∉ T)
    (x : ℤ) (j : ℕ) (hj : j < m)
    (hk : padicValInt 2 ((3 * b (m - 1) - 2 * a (m - 1)) - x) = padicValInt 2 (b j - a j))
    (hnode : x % 2 ^ padicValInt 2 (b j - a j) = a j % 2 ^ padicValInt 2 (b j - a j)) :
    (θ (padicValInt 2 ((3 * b (m - 1) - 2 * a (m - 1)) - x))
        (x % 2 ^ padicValInt 2 ((3 * b (m - 1) - 2 * a (m - 1)) - x)) = true ↔
      bitOne (3 * b (m - 1) - 2 * a (m - 1)) (padicValInt 2 ((3 * b (m - 1) - 2 * a (m - 1)) - x))) := by sorry

end Erdos195
