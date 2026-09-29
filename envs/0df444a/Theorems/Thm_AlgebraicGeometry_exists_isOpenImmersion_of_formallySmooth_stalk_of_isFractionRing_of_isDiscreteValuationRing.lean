-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/00735034-1d1a-5740-b1a3-50d578166967
-- title:
--   Formally smooth birational map is an open immersion near a DVR point
-- statement:
--   Let $v \colon U \to W$ be a morphism of schemes that is locally of finite type, with $W$ locally Noetherian, and let $x$ be a point of $U$ whose local ring $O := \mathcal{O}_{U,x}$ is an integral domain and a discrete valuation ring. Write $O' := \mathcal{O}_{W,v(x)}$ and let $v^\sharp_x \colon O' \to O$ be the induced map on stalks. Assume given an element $\pi \in O'$ with $\pi \neq 0$ such that the ideal $(\pi)$ of $O'$ is prime. Assume further that, when $\operatorname{Frac}(O)$ is regarded as an $O'$-algebra via the composite of $v^\sharp_x$ with $O \to \operatorname{Frac}(O)$, this makes $\operatorname{Frac}(O)$ a fraction ring (localisation at the nonzero divisors, in Mathlib's sense) of $O'$; and that, when $O$ is regarded as an $O'$-algebra via $v^\sharp_x$, the algebra $O$ is formally smooth over $O'$. Then there exists an open subscheme $V$ of $U$ with $x \in V$ such that the inclusion $V \hookrightarrow U$ followed by $v$ is an open immersion.
--
--   This is the local criterion of Bosch–Lütkebohmert–Raynaud for a morphism that is birational and formally smooth at a point with discrete valuation local ring to be an open immersion in a neighbourhood of that point. It serves the construction of Néron models in this development, where it is applied at a maximal point of a special fibre to recognise translation maps as open immersions; it is used in the smoothness and component-counting steps of that construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : letI : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : letI : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) := by sorry
