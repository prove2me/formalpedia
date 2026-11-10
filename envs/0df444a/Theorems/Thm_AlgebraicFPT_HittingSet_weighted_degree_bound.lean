-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_weighted_degree_bound
-- name    : AlgebraicFPT.HittingSet.weighted_degree_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:43.894107+00:00
-- url     : https://prove2.me/theorems/754481a4-9f1b-4823-b25e-6a8c14b255ad
-- title:
--   Lemma 3.1 — Weighted degree bound
-- statement:
--   Let $n,m\ge0$ and $d\ge1$ be natural numbers, and let $f_1,\ldots,f_m\in\mathbb C[z_1,\ldots,z_n]$ have total degree at most $d$. For the whole collection $\mathcal X$ of Zariski irreducible components of the common zero locus, there is a finite enumeration of exactly $\mathcal X$. Every enumerated component $Z$ has a finite codimension $c_Z$ and a finite positive degree $\delta_Z=\deg Z$, and
--   $$\sum_{Z\in\mathcal X}\frac{\delta_Z}{d^{c_Z}}\le1,\qquad
--   \forall k\ge0,\quad \#\{Z\in\mathcal X:c_Z\le k\}\le d^k.$$
--   Degree means the degree of the projective closure, represented by the published Heintz degree. The finite natural witnesses equal that extended-natural degree; no infinite value is converted to zero.
--
--   This bound applies to arbitrary finite polynomial systems, including systems with components of different dimensions. It is the geometric dependency for the bounded-rank hitting-set result. Empty systems, constant or zero polynomials, $n=0$, and $k=0$ are included.
--
--   Differences from the source:
--   - encoding: a finite complex polynomial system, its component sum and ordinary component counts → Fin-indexed variables and equations, a finite enumeration of all components with finite dimension and degree witnesses, and extended-natural component counts; reason: the enumeration and finite positive degree and codimension witnesses are conclusions; the weighted sum has exactly the source values and finite cardinal bounds exclude infinity without a default conversion
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), p.5, Lemma 3.1; Appendix A, pp.15–16

import Definitions.Def_AlgebraicFPT_HittingSet_Geometry

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet

/-- Lemma 3.1, p.5; Appendix A, pp.15–16. The finite enumeration, finite positive
Heintz degrees, and finite actual codimensions below are conclusions, not input
assumptions. X enumerates ALL components of the entire zero locus. -/
theorem weighted_degree_bound (n m d : ℕ) (hd : 1 ≤ d)
    (f : Fin m → MvPolynomial (Fin n) ℂ) (hf : ∀ i, (f i).totalDegree ≤ d) :
    ∃ (X : Finset (Set (Fin n → ℂ))) (c δ : Set (Fin n → ℂ) → ℕ),
      (X : Set (Set (Fin n → ℂ))) = components (RSCapacity.zeroSet (Set.range f)) ∧
      (∀ Z ∈ X, HasCodim Z (c Z) ∧ RSCapacity.heintzDeg Z = (δ Z : ℕ∞) ∧ 0 < δ Z) ∧
      (∑ Z ∈ X, (δ Z : ℝ) / (d : ℝ) ^ c Z) ≤ 1 ∧
      (∀ k : ℕ, (lowComponents (RSCapacity.zeroSet (Set.range f)) k).encard ≤
        (d ^ k : ℕ)) := by sorry

end AlgebraicFPT.HittingSet
