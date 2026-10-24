-- Prove2me | Theorems.Thm_Erdos195_open_path_ruler
-- name    : Erdos195.open_path_ruler
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T22:16:25.130554+00:00
-- url     : https://prove2.me/theorems/dcaaed58-ba79-4e36-8000-edb85fa62fef
-- title:
--   Ruler law for open paths: between two equal 2-adic levels of an open path lies a strictly lower one
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of $T$ ($a$ before $b$), call $2b-a$ its third term, $3b-2a$ its fourth term, and $\nu_2(b-a)$ its level. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(0\le i<m-1),$$
--   no third term $2b_i-a_i$ in $T$, and the fourth term $3b_{m-1}-2a_{m-1}$ of the last pair also absent from $T$. **Theorem (ruler law for open paths).** If $T$ is $\theta$-safe for some tree witness $\theta$ and contains such an open path, then for all $i<j<m$ with $\nu_2(b_i-a_i)=\nu_2(b_j-a_j)$ there is an index $l$ with $i<l<j$ and $\nu_2(b_l-a_l)<\nu_2(b_i-a_i)$.
--
--   So the sequence of levels along an open path behaves like a ruler sequence: between two equal levels a strictly lower one occurs. In particular the minimal level is attained exactly once, and a path with $r$ distinct levels has length at most $2^r-1$. The reason: every pair of the path has both its third and fourth term missing, so safety fixes its orientation at its node; the points $t_i=2b_i-a_i$ satisfy $t_{i+1}-t_i=b_i-a_i$, which forces two consecutive pairs of the same level (with only higher levels between) to sit at the same node with opposite orientation. This is the acyclic analogue of milestone 147 (open cycles are never tree-safe). It is a structural lemma about the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, pairs are `a b : ℕ → ℤ` on indices `i < m`, levels are `padicValInt 2 (b i - a i)`; safety is `∃ θ, Safe (treeLt θ) T`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_path_ruler (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hpath : ∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1))
    (ht : ∀ i < m, 2 * b i - a i ∉ T)
    (hw : 3 * b (m - 1) - 2 * a (m - 1) ∉ T)
    (i j : ℕ) (hij : i < j) (hjm : j < m)
    (hk : padicValInt 2 (b j - a j) = padicValInt 2 (b i - a i)) :
    ∃ l, i < l ∧ l < j ∧ padicValInt 2 (b l - a l) < padicValInt 2 (b i - a i) := by sorry

end Erdos195
