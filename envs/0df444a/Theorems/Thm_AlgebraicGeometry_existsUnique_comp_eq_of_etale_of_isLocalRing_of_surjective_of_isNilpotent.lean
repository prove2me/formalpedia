-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
-- name    : AlgebraicGeometry.existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/497cabfd-f386-5a4b-ba98-47c56e6d3b91
-- title:
--   Unique infinitesimal lifting along étale morphisms over local rings
-- statement:
--   Let $p : X \to Y$ be an étale morphism of schemes (in the universe $u$), and let $B$, $C$ be commutative local rings in the same universe. Let $\pi : B \to C$ be a ring homomorphism which is surjective and whose kernel is a nilpotent ideal of $B$. Let $Q : \operatorname{Spec} B \to Y$ and $a_0 : \operatorname{Spec} C \to X$ be morphisms of schemes such that $a_0$ followed by $p$ equals $\operatorname{Spec}(\pi)$ followed by $Q$, i.e. $p \circ a_0 = Q \circ \operatorname{Spec}(\pi)$, where $\operatorname{Spec}(\pi) : \operatorname{Spec} C \to \operatorname{Spec} B$ is the morphism induced by $\pi$. Then there is exactly one morphism $Q' : \operatorname{Spec} B \to X$ such that $Q'$ followed by $p$ equals $Q$ and $\operatorname{Spec}(\pi)$ followed by $Q'$ equals $a_0$; that is, $p \circ Q' = Q$ and $Q' \circ \operatorname{Spec}(\pi) = a_0$. Both existence and uniqueness of the lift are asserted.
--
--   This is the unique infinitesimal lifting property characterising formally étale morphisms, specialised to test rings that are local and to nilpotent (rather than merely square-zero) kernels; taking $B$ the dual numbers over a field and $C$ that field, it expresses that an étale morphism induces a bijection on tangent vectors. It is used in the construction of fake elliptic curves in the Čerednik–Drinfeld part of the development, in [`CerednikDrinfeld.QM.FakeEllipticCurve.act_trace_of_etale`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.act_trace_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p]
    {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (Q : Spec (CommRingCat.of B) ⟶ Y) (a₀ : Spec (CommRingCat.of C) ⟶ X)
    (h : a₀ ≫ p = Spec.map (CommRingCat.ofHom π) ≫ Q) :
    ∃! Q' : Spec (CommRingCat.of B) ⟶ X, Q' ≫ p = Q ∧ Spec.map (CommRingCat.ofHom π) ≫ Q' = a₀ := by sorry
