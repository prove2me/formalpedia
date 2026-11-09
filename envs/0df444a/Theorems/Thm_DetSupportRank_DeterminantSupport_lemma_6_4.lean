-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_6_4
-- name    : DetSupportRank.DeterminantSupport.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:19.91577+00:00
-- url     : https://prove2.me/theorems/9e8051fe-16cb-48c3-9815-9c7bd0f2b097
-- title:
--   Lemma 6.4 — Complex permutation concentration
-- statement:
--   Let $n\ge3$, let $v\in\mathbb C^n$ have pairwise distinct coordinates, and let $w\in\mathbb R^n$ have coordinates which are not all equal. For every $c\in\mathbb C$,
--   $$\Pr_{\sigma\in S_n}[w\cdot v^\sigma=c]\le\begin{cases}1/n,&n\text{ odd},\\1/(n-1),&n\text{ even}.\end{cases}$$
--   The probability is uniform over all permutations. There is no nonzero-sum condition on $v$, and the coefficient vector $w$ remains real.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: uniform probabilities on a finite permutation set → exact rational cardinality divided by n!; reason: the rational number embeds into the real probability with the same order and values
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 6.4, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Permutations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 6.4, p.27. -/
theorem lemma_6_4 {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℂ)
    (hv : Function.Injective v) (w : Fin n → ℝ) (hw : ∃ i j, w i ≠ w j) (c : ℂ) :
    permutationProbability (fun σ => ∑ i, (w i : ℂ) * v (σ i) = c) ≤
      if Odd n then (1 : ℚ) / (n : ℚ) else (1 : ℚ) / ((n - 1 : ℕ) : ℚ) := by sorry

end DetSupportRank.DeterminantSupport
