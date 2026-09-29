-- Prove2me | Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq
-- name    : AlgebraicGeometry.formallyUnramified_of_forall_specMap_comp_eq_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/1c2d154b-31f9-546f-9476-21ed5c2a00d1
-- title:
--   Uniqueness of infinitesimal lifts implies formal unramifiedness
-- statement:
--   Let $S$ be a commutative ring, let $H$ be a scheme, and let $q : H \to \operatorname{Spec} S$ be a morphism of schemes (all in a single universe). Assume the following uniqueness property of infinitesimal points: for every pair of commutative rings $S'$, $S''$ and every ring homomorphism $\psi : S' \to S''$ which is surjective and whose kernel satisfies $(\ker \psi)^2 = 0$, for every morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every two morphisms $x_1, x_2 : \operatorname{Spec} S' \to H$ with $x_1$ followed by $q$ equal to $s$ and $x_2$ followed by $q$ equal to $s$, if $\operatorname{Spec}(\psi) : \operatorname{Spec} S'' \to \operatorname{Spec} S'$ followed by $x_1$ agrees with $\operatorname{Spec}(\psi)$ followed by $x_2$, then $x_1 = x_2$. (Since $s$ is quantified over, the two conditions over $s$ amount to $x_1$ and $x_2$ having the same composite with $q$; no existence of lifts is assumed, only their uniqueness.) The conclusion is that $q$ satisfies Mathlib's predicate `FormallyUnramified`, the affine-local morphism property associated with formally unramified ring homomorphisms.
--
--   This is the functor-of-points form of the infinitesimal criterion for formal unramifiedness: uniqueness of lifts of $S$-points along square-zero thickenings of affine test schemes suffices, the target being affine. It is used in the construction of schemes of morphisms, where the relevant uniqueness statement (two homomorphisms agreeing modulo a nilpotent ideal coincide) is available directly, in [`GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_specMap_comp_eq_imp_eq
    {S : Type u} [CommRing S] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of S))
    (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S''), Function.Surjective ψ →
      RingHom.ker ψ ^ 2 = ⊥ →
      ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H),
        x₁ ≫ q = s → x₂ ≫ q = s →
        Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
    FormallyUnramified q := by sorry
