-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_path_prefix_partition
-- name    : AnonymousDirectedCounting.Exact.Supplement.path_prefix_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:46.608745+00:00
-- url     : https://prove2.me/theorems/9f43ee7e-b58f-4395-adbc-c1f8ccbfea36
-- title:
--   Lemma 15 — common path prefix and its partition
-- statement:
--   With the Appendix F data, let $a_0,\dots,a_m$ be group sizes with $a_i\ge B$ and $\sum_ic_ia_i=C$, and run the path graph in rounds $1,\dots,B-1$.
--
--   1. The labeled history-tree prefix through level $B-1$, without fiber cardinalities, is the same for all such size vectors.
--   2. After each round $r$ with $1\le r\le B-1$, group $i$ has the $r$ singleton classes $\{x_{i,1}\},\dots,\{x_{i,r}\}$ and the single nonempty suffix class $\{x_{i,r+1},\dots,x_{i,a_i}\}$.
--   3. After each such round, members of different groups have different histories.
--
--   For every $1\le r\le B-1$, the classes of group $i$ are
--   $$\{x_{i,1}\},\ldots,\{x_{i,r}\},\qquad\{x_{i,r+1},\ldots,x_{i,a_i}\}\ne\varnothing.$$
--
--   The common prefix is what allows a second network of a different order to reproduce the reference vista.
--
--   Differences from the source:
--   - encoding: the labeled history-tree prefix through round B − 1, without fiber cardinalities, is the same → historyLevel sets coincide at every level r ≤ B − 1; reason: History values are labeled nodes carrying parent, outdegree label and red edges and no cardinalities
--   - encoding: agents x_{i,1}, …, x_{i,a_i} → memberAt m a i k with 0-based k : Fin (a i), i.e. x_{i,k+1}; reason: indexing only
--   - encoding: the network of the lemma (path graph for rounds 1..B−1) → groupNetwork, the path graph before round B and the star afterwards; reason: rounds after r do not affect level-r histories
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 29 (PDF p. 31), Lemma 15

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_X3CReduction

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 15, printed p. 29 (PDF p. 31). For all group sizes `a_i ≥ B` with `∑ c_i a_i = C`, the
levels `0, …, B − 1` of the history tree (labeled nodes, without fiber cardinalities) are the same;
after each round `1 ≤ r ≤ B − 1`, group `i` has the `r` singleton classes `{x_{i,1}}, …, {x_{i,r}}`
and the single nonempty suffix class `{x_{i,r+1}, …, x_{i,a_i}}`; and members of different groups
have different histories. -/
theorem path_prefix_partition (q m : ℕ) (S : Fin m → Finset ℕ) (hS : IsX3CInstance q m S) :
    (∀ a a' : Fin (m + 1) → ℕ, (∀ i, baseB q ≤ a i) → (∀ i, baseB q ≤ a' i) →
      ∑ i, coef q m S i * a i = leaderDegree q m S →
      ∑ i, coef q m S i * a' i = leaderDegree q m S →
        ∀ r, r ≤ baseB q - 1 →
          historyLevel (groupNetwork q m S a) r = historyLevel (groupNetwork q m S a') r) ∧
    (∀ a : Fin (m + 1) → ℕ, (∀ i, baseB q ≤ a i) →
      ∑ i, coef q m S i * a i = leaderDegree q m S →
        ∀ r, 1 ≤ r → r ≤ baseB q - 1 →
          (∀ (i : Fin (m + 1)) (k : Fin (a i)), k.val < r →
            fiberOf (groupNetwork q m S a) r
              (history (groupNetwork q m S a) r (memberAt m a i k)) = {memberAt m a i k}) ∧
          (∀ i : Fin (m + 1), (suffixSet m a i r).Nonempty) ∧
          (∀ (i : Fin (m + 1)) (k : Fin (a i)), r ≤ k.val →
            fiberOf (groupNetwork q m S a) r
              (history (groupNetwork q m S a) r (memberAt m a i k)) = suffixSet m a i r) ∧
          (∀ (i i' : Fin (m + 1)) (k : Fin (a i)) (k' : Fin (a i')), i ≠ i' →
            history (groupNetwork q m S a) r (memberAt m a i k) ≠
              history (groupNetwork q m S a) r (memberAt m a i' k'))) := by sorry

end AnonymousDirectedCounting.Exact.Supplement
