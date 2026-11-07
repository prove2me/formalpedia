-- Prove2me | Theorems.Thm_AKSZigZag_lemma_5
-- name    : AKSZigZag.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:46.566255+00:00
-- url     : https://prove2.me/theorems/c7602104-2089-4632-bcfb-7cdda6f2230c
-- title:
--   Lemma 5, p.9 — misplaced counts never increase under standard switches
-- statement:
--   For contents $x$ on the registers $1,\dots,n$ and $1\le k\le n$, let
--   $$
--   \ell_k=|R(\{1,\dots,k\})\cap\{k+1,\dots,n\}|,\qquad h_k=|R(\{k+1,\dots,n\})\cap\{1,\dots,k\}|.
--   $$
--   So $\ell_k$ counts the elements larger than $k$ in the first $k$ registers, and $h_k$ counts the elements at most $k$ in the last $n-k$ registers. Then:
--   1. a single switch $(i,j)$ with $i<j$ (smaller element to $i$) increases neither $\ell_k$ nor $h_k$;
--   2. for every standard comparator network, neither count increases from one parallel step to the next.
--
--   The paper uses this tacitly throughout §8: elements once on the correct side of a cut never cross back in a way that increases the error.
--
--   Differences from the source:
--   - generalization: 1 ≤ k ≤ n, contents a permutation, throughout the algorithm → every k ∈ ℕ, any contents function, after every single switch and every parallel step of every standard network; reason: the paper's parenthetical states it for all such networks; k = 0 or k ≥ n gives zero counts, and permutations are particular contents
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, Lemma 5, p.9

import Mathlib
import Definitions.Def_AKSSorting_Core_compareExchange
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_NetworkOps

namespace AKSZigZag

open AKSSorting.Core

/-- **Lemma 5** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.9): "For any k, 1 ≤ k ≤ n, the
numbers |R({1,...,k}) ∩ {k+1,...,n}| and |R({k+1,...,n}) ∩ {1,...,k}| change monotone decreasing
throughout the algorithm. (This is clearly true for all comparator networks in which switches
place the larger element to the larger register.)"

For contents `x : Fin n → Fin n`, write `low k x` for the number of the first `k` registers
holding an element `> k` and `high k x` for the number of the last `n - k` registers holding an
element `≤ k` (1-based). Then
1. a single switch `(i, j)` with `i < j` increases neither count;
2. for every standard network, neither count increases from one parallel step to the next.

**Formalization Note.** 0-based: `low k x = #{i | i < k ∧ k ≤ x i}`,
`high k x = #{i | k ≤ i ∧ x i < k}`. The contents may be any function (not only a permutation)
and `k` any natural number; for `k = 0` or `k ≥ n` both counts are `0`. -/
theorem lemma_5 {n : ℕ} :
    (∀ i j : Fin n, i < j → ∀ (x : Fin n → Fin n) (k : ℕ),
      (Finset.univ.filter fun r : Fin n => r.val < k ∧ k ≤ (compareExchange i j x r).val).card ≤
          (Finset.univ.filter fun r : Fin n => r.val < k ∧ k ≤ (x r).val).card ∧
        (Finset.univ.filter fun r : Fin n => k ≤ r.val ∧ (compareExchange i j x r).val < k).card ≤
          (Finset.univ.filter fun r : Fin n => k ≤ r.val ∧ (x r).val < k).card) ∧
    (∀ N : ComparatorNetwork n, IsStandard N → ∀ (x : Fin n → Fin n) (k ℓ : ℕ),
      (Finset.univ.filter fun r : Fin n =>
          r.val < k ∧ k ≤ ((prefixNet N (ℓ + 1)).eval x r).val).card ≤
        (Finset.univ.filter fun r : Fin n => r.val < k ∧ k ≤ ((prefixNet N ℓ).eval x r).val).card ∧
      (Finset.univ.filter fun r : Fin n =>
          k ≤ r.val ∧ ((prefixNet N (ℓ + 1)).eval x r).val < k).card ≤
        (Finset.univ.filter fun r : Fin n => k ≤ r.val ∧ ((prefixNet N ℓ).eval x r).val < k).card) := by sorry

end AKSZigZag
