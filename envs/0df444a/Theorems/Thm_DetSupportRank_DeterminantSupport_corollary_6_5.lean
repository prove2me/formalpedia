-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_corollary_6_5
-- name    : DetSupportRank.DeterminantSupport.corollary_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:30.279388+00:00
-- url     : https://prove2.me/theorems/9aef8bfa-79e3-4756-b53a-056ea4356ac9
-- title:
--   Corollary 6.5 — Partial-sum permutation concentration
-- statement:
--   Let $n\ge3$, let $v\in\mathbb C^n$ have pairwise distinct coordinates, let $\varnothing\ne A\subsetneq[n]$, and let $c\in\mathbb C$. Then
--   $$\Pr_{\sigma\in S_n}\left[\sum_{i\in A}v_{\sigma(i)}=c\right]\le\begin{cases}1/n,&n\text{ odd},\\1/(n-1),&n\text{ even}.\end{cases}$$
--   Every nonempty proper subset and every complex target value are retained, with the exact parity constants.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: uniform probabilities on a finite permutation set → exact rational cardinality divided by n!; reason: this is the same finite uniform probability, represented exactly
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Corollary 6.5, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Permutations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Corollary 6.5, p.28. -/
theorem corollary_6_5 {n : ℕ} (hn : 3 ≤ n) (v : Fin n → ℂ)
    (hv : Function.Injective v) (A : Finset (Fin n)) (ha : A.Nonempty)
    (hproper : A ≠ Finset.univ) (c : ℂ) :
    permutationProbability (fun σ => ∑ i ∈ A, v (σ i) = c) ≤
      if Odd n then (1 : ℚ) / (n : ℚ) else (1 : ℚ) / ((n - 1 : ℕ) : ℚ) := by sorry

end DetSupportRank.DeterminantSupport
