-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
-- name    : AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/c2e36e95-0575-5308-936a-9f27b530131a
-- title:
--   A valuation subring of K(X) has at most one centre
-- statement:
--   Let $O$ be a commutative ring and let $X$ be a scheme that is integral, equipped with a morphism $f : X \to \operatorname{Spec} O$ that is separated. Let $V$ be a valuation subring of the function field $K(X)$ of $X$ (the stalk of the structure sheaf at the generic point, viewed as a field), and let $c_1, c_2$ be points of $X$. Assume, for $i = 1, 2$, that the local ring $\mathcal{O}_{X,c_i}$ (the stalk of `X.presheaf` at $c_i$) is carried into $V$ by the canonical algebra map $\mathcal{O}_{X,c_i} \to K(X)$, i.e. every element of the stalk has image in $V$, and moreover that every element of the maximal ideal of $\mathcal{O}_{X,c_i}$ has image in the non-units of $V$; in other words $V$ dominates $\mathcal{O}_{X,c_i}$ along the canonical map. The conclusion is $c_1 = c_2$.
--
--   This is the uniqueness half of the valuative criterion of separatedness: a valuation subring of the function field of a separated integral scheme has at most one centre. It is used, together with the corresponding existence statement, in the theory of integral curves over a base, for instance to identify the unique point whose local ring is a given discrete valuation ring and to compare local rings along specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated
    {O : Type u} [CommRing O] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (V : ValuationSubring X.functionField) (c₁ c₂ : X)
    (h₁ : ∀ s : X.presheaf.stalk c₁, algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V)
    (h₁' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₁),
      algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V.nonunits)
    (h₂ : ∀ s : X.presheaf.stalk c₂, algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V)
    (h₂' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₂),
      algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V.nonunits) :
    c₁ = c₂ := by sorry
