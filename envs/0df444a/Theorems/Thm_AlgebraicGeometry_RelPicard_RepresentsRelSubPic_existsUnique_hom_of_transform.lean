-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/66951236-2efe-532d-9f48-3e3155cdcfb1
-- title:
--   Unique morphism of representing schemes induced by a transformation
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$, $c' : C' \to \operatorname{Spec} R$ be schemes over $R$ equipped with sections $\varepsilon, \varepsilon'$ (morphisms to $C$, resp. $C'$, from $\operatorname{Spec} R$ composing with $c$, resp. $c'$, to the identity). Let $P$, $P'$ be sub-Picard conditions for $(c,\varepsilon)$, $(c',\varepsilon')$: predicates on rigidified line bundles (invertible modules on $C \times_R T$ whose pullback along the rigidifying section is trivial) that hold for the unit bundle, depend only on the isomorphism class of the underlying module, and are stable under pullback along $R$-morphisms $T' \to T$. Assume $h$, $h'$ exhibit designations $D$, $D'$ (schemes over $R$ with a zero section) as representing these conditions, with Poincaré bundles and the universal property giving, for each $M$ satisfying the condition over $t : T \to \operatorname{Spec} R$, a unique $R$-morphism `classify` $T \to D$ pulling the Poincaré bundle back to $M$ up to isomorphism of modules. Let $\Phi$ send rigidified line bundles for $(c',\varepsilon')$ over any $t$ to ones for $(c,\varepsilon)$ over $t$, such that $\Phi$ preserves isomorphism of underlying modules (`hcongr`), commutes with pullback along $R$-morphisms up to isomorphism of underlying modules (`hnat`), and carries $P'$ into $P$ (`hcut`). Then there is a unique $R$-morphism $\varphi : D' \to D$ such that for every $t : T \to \operatorname{Spec} R$ and every $M$ satisfying $P'$, the classifying morphism of $M$ followed by $\varphi$ equals the classifying morphism of $\Phi(M)$.
--
--   This is the Yoneda-type transfer principle for representable rigidified relative Picard conditions: a transformation of the represented functors, given concretely by an operation $\Phi$ on rigidified line bundles compatible with isomorphism and base change, induces a unique morphism of the representing schemes compatible with classifying morphisms. It is the mechanism by which pullback along a morphism of pointed curves, the norm along a finite locally free morphism, and the resulting Hecke operators on Jacobians of modular curves are produced as morphisms of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u
set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicCondition c ε} {P' : SubPicCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c' ε' P' D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcongr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty (M.L ≅ M'.L) → Nonempty ((Φ t M).L ≅ (Φ t M').L))
    (hnat : ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t),
      Nonempty (((Φ t M).pullbackAlong ψ).L ≅ (Φ t' (M.pullbackAlong ψ)).L))
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M)) :
    ∃! φ : SchemeHomOver D'.toBase D.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) := by sorry
