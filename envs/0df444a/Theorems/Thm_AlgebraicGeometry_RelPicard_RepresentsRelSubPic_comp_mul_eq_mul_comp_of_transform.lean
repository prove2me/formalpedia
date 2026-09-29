-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c9e4b93a-fca2-5ec7-969f-92fc2f2b13d6
-- title:
--   Multiplicative transformations induce homomorphisms of representing Picard schemes
-- statement:
--   Fix a commutative ring $R$ and two schemes $C,C'$ with morphisms $c : C \to \operatorname{Spec} R$, $c' : C' \to \operatorname{Spec} R$, each equipped with a section $\varepsilon$, resp. $\varepsilon'$, of its structure morphism. Let $P$ and $P'$ be conditions on rigidified line bundles (for $c,\varepsilon$ and $c',\varepsilon'$ respectively) that are closed under tensor product and under the inverse rule 'if $L \otimes M$ has underlying module isomorphic to the unit and $L$ satisfies the condition, then so does $M$', and let $D$, $D'$ be designations, i.e. schemes over $\operatorname{Spec} R$ together with a section of the structure morphism. Assume data $h$, $h'$ exhibiting $D$, $D'$ as representing the corresponding functors of rigidified bundles: a Poincaré bundle on the base of the designation satisfying the condition, the universal property that every rigidified bundle on $T$ satisfying the condition is the pullback of the Poincaré bundle along a unique $T$-point over $\operatorname{Spec} R$, and triviality of the pullback along the zero section. Let $\Phi$ assign, to every $t : T \to \operatorname{Spec} R$, a map from rigidified bundles for $(c',\varepsilon')$ over $t$ to rigidified bundles for $(c,\varepsilon)$ over $t$, such that $\Phi$ carries $P'$ into $P$ ($hcut$), and such that, as modules, $\Phi(M \otimes M').L \cong (\Phi M \otimes \Phi M').L$ and $\Phi(\mathcal{O}).L \cong \mathcal{O}.L$. Let $\varphi$ be a morphism from the base of $D'$ to the base of $D$ over $\operatorname{Spec} R$ such that for all $t$ and all $M$ satisfying $P'$, the classifying point of $M$ followed by $\varphi$ is the classifying point of $\Phi_t M$. The conclusion is twofold: for every $s : T \to \operatorname{Spec} R$ and all $T$-points $x,y$ of the base of $D'$ over $s$, the product $x \cdot y$ for the relative group law attached to $h'$, followed by $\varphi$, equals the product of $x$ followed by $\varphi$ and $y$ followed by $\varphi$ for the relative group law attached to $h$; and the zero section of $D'$ followed by $\varphi$ is the zero section of $D$.
--
--   This is the statement that a natural, tensor- and unit-compatible operation $\Phi$ on rigidified line bundles induces a morphism of the representing schemes which is a homomorphism for the relative group laws and respects the zero sections; it is the mechanism by which pullback along a map of curves, norm operations and Hecke correspondences are converted into genuine homomorphisms of relative Jacobians. It is used by the results constructing such homomorphisms from rigidified pullbacks and norm modules, and by the Abel–Jacobi constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicGroupCondition c ε} {P' : SubPicGroupCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M))
    (htensor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty ((Φ t (M.tensor M')).L ≅ ((Φ t M).tensor (Φ t M')).L))
    (hunit : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      Nonempty ((Φ t (RigidifiedLineBundle.unit t)).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L))
    (φ : SchemeHomOver D'.toBase D.toBase)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM)) :
    (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D'.toBase),
      NeronModelInfra.schemeHomOverComp (h'.relativeGroupLaw.mul s x y) φ =
        h.relativeGroupLaw.mul s (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) ∧
    D'.zeroSection ≫ φ.1 = D.zeroSection := by sorry
