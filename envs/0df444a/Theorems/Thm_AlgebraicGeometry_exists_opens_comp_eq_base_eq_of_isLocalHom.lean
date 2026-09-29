-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom
-- name    : AlgebraicGeometry.exists_opens_comp_eq_base_eq_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/e5921580-cd70-55e2-9fc6-63e10e1491ba
-- title:
--   Spreading out a lift over the spectrum of a local ring
-- statement:
--   Let $X$, $Y$, $Y'$ be schemes, $U \subseteq X$ an open subscheme, $\alpha : U \to Y$ a morphism, and $z \in X$ a point lying in $U$ at which $X$ satisfies the germ-injectivity condition `IsGermInjectiveAt` (injectivity of the germ maps into the stalk at $z$ on suitable neighbourhoods, as holds for instance when $X$ is integral). Let $\beta : Y' \to Y$ be locally of finite type, let $O$ be a local commutative ring, and let $\ell_0 : \operatorname{Spec} O \to Y$ and $\ell : \operatorname{Spec} O \to Y'$ be morphisms with $\ell$ followed by $\beta$ equal to $\ell_0$. Finally let $\varphi : O \to \mathcal{O}_{X,z}$ be a local ring homomorphism such that $\operatorname{Spec}\varphi$ followed by $\ell_0$ equals the canonical morphism $\operatorname{Spec}\mathcal{O}_{X,z} \to U$ (given by `Scheme.Opens.fromSpecStalkOfMem`) followed by $\alpha$. The conclusion asserts the existence of an open $U' \subseteq U$ of $X$ containing $z$ and a morphism $\alpha' : U' \to Y'$ such that $\alpha'$ followed by $\beta$ equals the inclusion $U' \to U$ followed by $\alpha$, and such that $\alpha'$ sends the point $z$ of $U'$ to the image under $\ell$ of the closed point of $\operatorname{Spec} O$.
--
--   This is a spreading-out statement in the style of EGA IV, 8.13: a lift of $\alpha$ through a morphism locally of finite type, given only over the spectrum of a local ring mapping to the stalk at $z$, extends to a lift over an open neighbourhood of $z$, with prescribed image of $z$. It is used in the construction of the proper morphism with prescribed behaviour at a point of one-dimensional stalk, in [`AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_opens_comp_eq_base_eq_of_isLocalHom
    {X Y Y' : Scheme.{u}} (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (z : X) (hzU : z ∈ U)
    [X.IsGermInjectiveAt z]
    (β : Y' ⟶ Y) [LocallyOfFiniteType β]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y) (ℓ : Spec (CommRingCat.of O) ⟶ Y') (hℓ : ℓ ≫ β = ℓ₀)
    (φ : CommRingCat.of O ⟶ X.presheaf.stalk z) [IsLocalHom φ.hom]
    (hφ : Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α) :
    ∃ (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U') (α' : (U' : Scheme.{u}) ⟶ Y'),
      α' ≫ β = X.homOfLE hU' ≫ α ∧ α'.base ⟨z, hzU'⟩ = ℓ.base (IsLocalRing.closedPoint O) := by sorry
