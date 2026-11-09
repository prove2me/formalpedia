-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_proposition_3_10
-- name    : DetSupportRank.DeterminantSupport.proposition_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:59.921242+00:00
-- url     : https://prove2.me/theorems/cf005707-163d-4161-bc69-4528f6a293a2
-- title:
--   Proposition 3.10 — Koszul relations
-- statement:
--   Let $f$ be a nonzero set-multilinear polynomial in positive numbers of row parts and variables per row, over any field. Let $r\ge1$, let $g_1,\ldots,g_r$ be homogeneous of annotated degrees $d_i\in\mathbb N^d$, and assume $f\in(g_1,\ldots,g_r)$. There are nonnegative integers $c_I$ and vectors $v_I\in\mathbb N^d$ for all $I\subseteq[r]$ such that
--   $$v_I=-\sum_{i\in I}d_i+c_I\mathbf1,\qquad (v_I)_{|I|\text{ even}}\sim_f(v_I)_{|I|\text{ odd}}.$$
--   Zero generators may carry any homogeneous degree annotation. The relation is the source's polynomial-matrix relation, with no imposed rank bound.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: degrees of homogeneous generators, including zero generators → explicit degree annotations for every generator; reason: zero has no unique degree; all permitted homogeneous annotations remain available
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 3.10, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Proposition 3.10, p.7. -/
theorem proposition_3_10 {K : Type*} [Field K] {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (f : MvPolynomial (Fin d × Fin m) K) (hf : f ≠ 0)
    (hml : SetMultCost.IsSetMultilinearOn Prod.fst Finset.univ f)
    {r : ℕ} (hr : 1 ≤ r) (g : Fin r → MvPolynomial (Fin d × Fin m) K)
    (deg : Fin r → Fin d → ℕ)
    (hg : ∀ i, Homogeneous rowWeight (fun j => (deg i j : ℤ)) (g i))
    (hideal : f ∈ Ideal.span (Set.range g)) :
    ∃ (c : Finset (Fin r) → ℕ) (v : Finset (Fin r) → Fin d → ℕ),
      (∀ I j, (v I j : ℤ) = -(∑ i ∈ I, (deg i j : ℤ)) + (c I : ℤ)) ∧
      DegreeRelation f
        (fun I : {I : Finset (Fin r) // Even I.card} => v I.val)
        (fun I : {I : Finset (Fin r) // Odd I.card} => v I.val) := by sorry

end DetSupportRank.DeterminantSupport
