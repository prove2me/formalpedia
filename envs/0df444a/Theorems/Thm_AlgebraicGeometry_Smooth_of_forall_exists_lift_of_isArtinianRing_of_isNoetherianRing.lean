-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
-- name    : AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/6d28ee4e-815e-520e-ad75-713c7cbc92e6
-- title:
--   Artinian-local lifting criterion for smoothness over a Noetherian base
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $M$ be a scheme (all data in universe $0$), and let $\varpi \colon M \to \operatorname{Spec} R$ be a morphism of schemes that is locally of finite presentation. Assume the following lifting property: for every commutative ring $T'$ which is local and Artinian and whose residue field is algebraically closed, every nontrivial commutative ring $T$, and every surjective ring homomorphism $p \colon T' \to T$ such that $\ker p \cdot \mathfrak m_{T'} = 0$ (the product of ideals being the zero ideal), and for every morphism $s \colon \operatorname{Spec} T' \to \operatorname{Spec} R$ and every morphism $m \colon \operatorname{Spec} T \to M$ with $m$ followed by $\varpi$ equal to $\operatorname{Spec}(p)$ followed by $s$, there exists a morphism $m' \colon \operatorname{Spec} T' \to M$ with $m'$ followed by $\varpi$ equal to $s$, and $\operatorname{Spec}(p)$ followed by $m'$ equal to $m$. Then $\varpi$ is smooth. No uniqueness of the lift $m'$ is assumed.
--
--   This is the infinitesimal (formal) criterion of smoothness in the form in which only test rings that are Artinian local with algebraically closed residue field, and only small surjections $\ker p \cdot \mathfrak m_{T'} = 0$, need be checked, the base being Noetherian and the morphism locally of finite presentation. It is used in the étale analogue [`AlgebraicGeometry.Etale.of_forall_existsUnique_lift_of_isArtinianRing_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Etale.of_forall_existsUnique_lift_of_isArtinianRing_of_isNoetherianRing), where the lifts are in addition required to be unique.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ϖ]
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    Smooth ϖ := by sorry
