-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_theorem_1_1
-- name    : DetSupportRank.DeterminantSupport.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:39.722686+00:00
-- url     : https://prove2.me/theorems/b365e9e3-08dd-4f05-b626-2cb2f4f32ade
-- title:
--   Theorem 1.1 — Optimal lower bound for all determinant-support polynomials
-- statement:
--   Let $F$ be any field, let $n>2$, and choose independent nonzero coefficients $c_\sigma\in F^\times$ for every permutation. For the formal polynomial
--   $$D=\sum_{\sigma\in S_n}c_\sigma\prod_{i=1}^n x_{i,\sigma(i)},$$
--   the full partition rank satisfies
--   $$\operatorname{PR}_F(D)\ge\begin{cases}n,&n\text{ odd},\\n-1,&n\text{ even}.\end{cases}$$
--   Partition factors may split the rows along any nonempty proper subset, independently in every summand. The theorem includes finite fields and characteristic two, with parity determined only by the integer $n$.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
--   - encoding: minimum finite decomposition length and hyperplane-covering size → infimum of actual witness lengths in ℕ∞, with empty infimum ∞; reason: on the source domain partition rank is finite and attained by a row expansion; the separate attainment target records this, and Theorem 3.9 also implies finite covering rank
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 1.1, p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Theorem 1.1, p.2. -/
theorem theorem_1_1 {K : Type*} [Field K] {n : ℕ}
    (hn : 2 < n) (c : Equiv.Perm (Fin n) → Kˣ) :
    (if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) ≤
      partitionRank (determinantSupportPolynomial c) := by sorry

end DetSupportRank.DeterminantSupport
