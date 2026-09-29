-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
-- name    : AlgebraicGeometry.exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a06243c5-6aa6-5412-b6c6-b782ea0a230f
-- title:
--   R-points via a universally closed open part of X
-- statement:
--   Let $R$ be a valuation domain with fraction field $K$, realised through an $R$-algebra structure on the field $K$ making $K$ a fraction field of $R$. Let $X$, $Xf$ and $X'$ be schemes, $g \colon X \to \operatorname{Spec} R$ a morphism, $i \colon Xf \to X$ an open immersion such that the composite $i$ followed by $g$ is universally closed, and $j \colon X' \to X$ an arbitrary morphism. Assume that on underlying topological spaces the images of $i$ and $j$ cover $X$, i.e. $\operatorname{range}(i) \cup \operatorname{range}(j)$ is all of $X$, and that the closed point of $R$ does not lie in the image of $j$ followed by $g$, so that $X'$ has empty special fibre. Let $x \colon \operatorname{Spec} K \to X$ be a $K$-point lying over $\operatorname{Spec} R$, that is, $x$ followed by $g$ equals $\operatorname{Spec}$ of the structure map $R \to K$. Then the following are equivalent: there is a section $s \colon \operatorname{Spec} R \to X$ of $g$ (so $s$ followed by $g$ is the identity) whose restriction along $\operatorname{Spec}(R \to K)$ is $x$; and $x$ factors through $i$, i.e. there is $xf \colon \operatorname{Spec} K \to Xf$ with $xf$ followed by $i$ equal to $x$.
--
--   This is a form of the existence part of the valuative criterion, packaged so that $R$-points of $X$ extending a given $K$-point are detected by the universally closed (for instance finite or proper) open part $Xf$ of $X$, the complementary piece $X'$ being irrelevant because it has empty special fibre. It is used in the counting of sections over local rings, for instance in the results bounding or computing the number of sections of a scheme over $\operatorname{Spec} R$ in terms of the special fibre, and in the production of sections for flat locally quasi-finite morphisms over henselian local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Xf X' : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [UniversallyClosed (i ≫ g)]
    (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (x : Spec (.of K) ⟶ X) (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    (∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) ↔
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = x := by sorry
