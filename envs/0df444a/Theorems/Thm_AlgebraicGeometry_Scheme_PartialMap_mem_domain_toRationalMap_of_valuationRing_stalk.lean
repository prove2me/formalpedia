-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
-- name    : AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7f7613c2-20a7-5410-aa74-b7c4ba1f96e3
-- title:
--   Valuation-ring stalks lie in the domain of the induced rational map
-- statement:
--   Let $X$, $Y$, $S$ be schemes and let $s_X : X \to S$, $s_Y : Y \to S$ be morphisms. Assume $X$ is integral (irreducible and reduced), $s_Y$ is locally of finite type, and $s_Y$ satisfies the existence half of the valuative criterion: every commutative square consisting of $\operatorname{Spec} K \to Y$ and $\operatorname{Spec} R \to S$, with $R$ a valuation ring and $K$ its fraction field, admits a lift $\operatorname{Spec} R \to Y$ making both triangles commute. Let $f$ be a partial map from $X$ to $Y$, that is, a dense open subscheme $f.\mathrm{domain}$ of $X$ together with a morphism $f.\mathrm{hom}$ from it to $Y$, and assume $f$ is a morphism over $S$ in the sense that $f.\mathrm{hom}$ followed by $s_Y$ equals the open immersion $f.\mathrm{domain}.\iota$ followed by $s_X$. Let $x$ be a point of $X$ whose local ring $\mathcal{O}_{X,x}$ is a valuation ring. Then $x$ lies in the domain of the rational map $f.\mathrm{toRationalMap}$ determined by $f$, i.e. some partial map equivalent to $f$ is defined at $x$.
--
--   This is the extension statement underlying the classical fact that a rational map from an integral scheme to a target satisfying the existence valuative criterion (for instance a proper target) is defined at every point with valuation-ring local ring. It is used in the project to extend partial maps and group-law data across such points, for example in the results on extending morphisms along open immersions into proper schemes and in the construction of maximal compatible partial actions for relative group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
    {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
    x ∈ f.toRationalMap.domain := by sorry
