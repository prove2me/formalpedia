-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classify_tensor
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.classify_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/74e88bc5-665f-506c-9902-a2ea1ac8e00c
-- title:
--   Classifying morphism of a tensor product is a product
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c\colon C\to\operatorname{Spec}R$ a morphism and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $P$ be a predicate on rigidified line bundles relative to $(c,\varepsilon)$ — for each $R$-scheme $t\colon T\to\operatorname{Spec}R$, on the data of a module $L$ on $C\times_{\operatorname{Spec}R}T$ that is locally isomorphic to the unit, together with a trivialisation of its pullback along the rigidifying section `rigSection` — which is closed under tensor product (`tensor_mem`) and satisfies the condition `inv_mem`. Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}R$ and a section of it, and let $h$ witness that $D$ represents the subfunctor cut out by $P$: a rigidified bundle `poincare` over $D.\mathrm{toBase}$ satisfying $P$ such that for every $t\colon T\to\operatorname{Spec}R$ and every rigidified $M$ satisfying $P$ there is a unique morphism $g\colon T\to D$ over $\operatorname{Spec}R$ with the pullback of `poincare` along $g$ isomorphic, as a module, to $M$, plus the normalisation along the zero section. For $L,M$ rigidified line bundles over $t$ both satisfying $P$, the assertion is that the morphism classifying $L\otimes M$ (with its induced rigidification) equals the product of the morphisms classifying $L$ and $M$, the product taken in the relative group law on $D.\mathrm{toBase}$ transported from the group-object structure on `Over.mk D.toBase` supplied by the representability of the sub-Picard commutative group presheaf.
--
--   This is the multiplicativity of the Poincaré bundle in the form of a dictionary between tensor product of rigidified line bundles and the group law on a representing object of the rigidified relative Picard functor. It is used when points of the representing scheme are computed from explicit divisor classes, for instance in the identification of points on the relative $\mathrm{Pic}^0$ of a model of $X_1$ with classes built by repeated tensoring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classify_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.classify_tensor
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t)
    (hL : P.P t L) (hM : P.P t M) :
    h.classify t (L.tensor M) (P.tensor_mem t L M hL hM) =
      h.relativeGroupLaw.mul t (h.classify t L hL) (h.classify t M hM) := by sorry
