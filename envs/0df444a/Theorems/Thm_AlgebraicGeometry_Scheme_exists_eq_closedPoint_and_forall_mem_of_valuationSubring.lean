-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring
-- name    : AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/24adcea0-5359-5c58-befe-04f0c486c33c
-- title:
--   Centre of a valuation on a universally closed integral scheme
-- statement:
--   Let $O$ be a commutative local ring, let $X$ be an integral scheme, and let $f : X \to \operatorname{Spec} O$ be a universally closed morphism. Write $\xi$ for the generic point of $X$ and $K(X)$ for the function field, the stalk at $\xi$, and let $\theta : O \to K(X)$ be the composite of the canonical identification of $O$ with the global sections of $\operatorname{Spec} O$, the map $f^\sharp$ on global sections, and the germ map $\Gamma(X,\mathcal O_X) \to K(X)$ at $\xi$. Let $V$ be a valuation subring of $K(X)$ and assume that $\theta(a) \in V$ for every $a \in O$, and that $\theta(a)$ is a non-unit of $V$ for every $a$ in the maximal ideal of $O$, i.e. $V$ dominates the image of $O$. The conclusion is that there exists a point $c \in X$ such that $f(c)$ is the closed point of $\operatorname{Spec} O$, such that the image in $K(X)$ of every element of the stalk $\mathcal O_{X,c}$ (under the algebra map to the function field) lies in $V$, and such that the image of every element of the maximal ideal of $\mathcal O_{X,c}$ is a non-unit of $V$; thus $V$ dominates $\mathcal O_{X,c}$.
--
--   This is the classical statement that a valuation of the function field dominating the base local ring has a centre on the special fibre, the existence half of the valuative criterion of properness in the form used in EGA II, §7.3. It is used in the project to identify local rings of normal proper curves and integral models with localisations or valuation rings, in particular by the results on unique centres on proper integrally closed curves and on affine models of normal schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring
    {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [UniversallyClosed f]
    (V : ValuationSubring X.functionField)
    (hOV : ∀ a : O, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ V)
    (hmV : ∀ a ∈ IsLocalRing.maximalIdeal O, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ V.nonunits) :
    ∃ c : X, f.base c = IsLocalRing.closedPoint O ∧
      (∀ s : X.presheaf.stalk c, algebraMap (X.presheaf.stalk c) X.functionField s ∈ V) ∧
      (∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c),
        algebraMap (X.presheaf.stalk c) X.functionField s ∈ V.nonunits) := by sorry
