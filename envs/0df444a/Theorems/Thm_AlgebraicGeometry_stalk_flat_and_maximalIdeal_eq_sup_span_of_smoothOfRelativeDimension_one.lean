-- Prove2me | Theorems.Thm_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/20314293-959f-5249-8e87-86527e66767f
-- title:
--   Stalk of a smooth relative curve at a closed point over the closed point
-- statement:
--   Let $W$ be a commutative noetherian local ring which is adically complete with respect to its maximal ideal and whose residue field is algebraically closed, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} W$ be a morphism that is smooth of relative dimension $1$. Let $x$ be a point of $X$ whose image under the underlying continuous map of $f$ is the closed point of $\operatorname{Spec} W$, and assume that $\{x\}$ is closed in $X$. Give the stalk $\mathcal{O}_{X,x}$ the $W$-algebra structure coming from the ring map obtained by composing the inverse of the canonical isomorphism $W \cong \Gamma(\operatorname{Spec} W, \mathcal{O})$, the map $f$ on global sections, and the germ map $\Gamma(X,\mathcal{O}_X) \to \mathcal{O}_{X,x}$. Then: $\mathcal{O}_{X,x}$ is a noetherian ring; the structure map $W \to \mathcal{O}_{X,x}$ is a local homomorphism; $\mathcal{O}_{X,x}$ is flat as a $W$-module; the composite $W \to \mathcal{O}_{X,x} \to \mathcal{O}_{X,x}/\mathfrak{m}_x$ is surjective; and there is an element $t \in \mathcal{O}_{X,x}$ with $\mathfrak{m}_x = \mathfrak{m}_W \mathcal{O}_{X,x} + (t)$ such that the Krull dimension of $\mathcal{O}_{X,x}/\mathfrak{m}_W\mathcal{O}_{X,x}$ equals $1$.
--
--   This is the local structure statement for a smooth relative curve at a closed point of the special fibre, packaged precisely as the hypotheses needed to identify the completion of the stalk with a power series ring in one variable over $W$; it is used by [`AlgebraicGeometry.exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one`](thm.html#AlgebraicGeometry.exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one). The proof cites the fact that a standard smooth algebra of relative dimension $1$ over a field has discrete valuation rings as localisations at maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
    (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    letI : Algebra W (X.presheaf.stalk x) :=
      ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)).toAlgebra
    IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalHom (algebraMap W (X.presheaf.stalk x)) ∧
      Module.Flat W (X.presheaf.stalk x) ∧
      Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap W (X.presheaf.stalk x))) ∧
      ∃ t : X.presheaf.stalk x,
        maximalIdeal (X.presheaf.stalk x) = (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x)) ⊔ Ideal.span {t} ∧
        ringKrullDim (X.presheaf.stalk x ⧸ (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x))) = 1 := by sorry
