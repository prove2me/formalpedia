-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_one_act
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.one_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/d930ac74-bca4-5ecd-8cef-76486d415394
-- title:
--   The identity theta point acts trivially on sections
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$, and let $L$ be a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} S$, with multiplication, unit and inverse satisfying associativity, the two unit laws and left inverse, and compatible with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\mathcal{L}$ be an object of `A.Modules`, let $R$ be a commutative ring and $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and write $\mathcal{L}_R$ for the pullback of $\mathcal{L}$ along the first projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to A$. Let $s$ be a section of $\mathcal{L}_R$ over the whole of $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$. The assertion is that the distinguished element $1$ of the type `ThetaPt f L 𝓛 t` of theta points — pairs consisting of a point of $A$ over $t$ together with an isomorphism between the pullback of $\mathcal{L}_R$ along the translation by that point and $\mathcal{L}_R$ itself — acts on $s$ as the identity: transporting $s$ by `act`, that is pulling $s$ back along the translation and applying the isomorphism of the theta point, returns $s$.
--
--   This is the unitality clause for the action of the theta group of $\mathcal{L}$ on global sections of $\mathcal{L}$ over the base change $A_R$, in the sense of Mumford's theory of theta groups; together with multiplicativity it makes the action a monoid, hence group, homomorphism into the endomorphisms of the section module. It is used in the construction of the commutator pairing attached to theta points and in the results on Schrödinger frames and their idempotent decompositions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_one_act.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.one_act
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    (1 : ThetaPt f L 𝓛 t).act s = s := by sorry
