-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_one_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/574d6e8a-8662-5c52-ac2b-7cc31f0af96c
-- title:
--   Pullback of the Poincaré bundle along the unit point is trivial
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a scheme over $R$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $P$ be a condition on rigidified line bundles on $(C,\varepsilon)$ that is closed under tensor product and has the cancellation property that if $L \otimes M$ has trivial underlying module then $P$ holds for $L$ whenever it holds for $M$; and let $D$ consist of a scheme together with a structure morphism $D \to \operatorname{Spec} R$ and a section of it. Assume $h$ witnesses that $D$ represents the subfunctor of the rigidified relative Picard functor of $(C,\varepsilon)$ cut out by $P$: it provides a rigidified line bundle $\mathcal P$ on $C \times_R D$ satisfying $P$, the universal property that every $P$-bundle on $C \times_R T$ is the pullback of $\mathcal P$ along a unique $T$-point of $D$ over $R$, and triviality of the pullback along the section of $D$. Then for every scheme $T$ with a morphism $t \colon T \to \operatorname{Spec} R$, the pullback of $\mathcal P$ along the unit $T$-point of the group law induced on relative points of $D$ by the representability has underlying module isomorphic to the structure sheaf of $C \times_R T$, that is, to the underlying module of the unit rigidified line bundle over $t$.
--
--   This is the unit law for the relative Picard scheme expressed on line bundles: the neutral element of the group law on $T$-points of $D$ classifies the trivial rigidified bundle. It is used together with the corresponding product rule to translate identities among $T$-points of relative Picard schemes into tensor-product and triviality statements about the classified bundles, and is invoked in the analysis of kernels of maps between such schemes and in the torus character-lattice computation for two glued smooth curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_one_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.one t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by sorry
