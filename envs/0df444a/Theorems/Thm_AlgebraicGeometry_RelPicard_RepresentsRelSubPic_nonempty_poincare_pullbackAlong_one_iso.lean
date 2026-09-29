-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/5f65ca88-3c9a-58b5-af86-0c4d664077d8
-- title:
--   Triviality of the Poincaré bundle at the unit point
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ be a scheme over $R$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $P$ be a `SubPicGroupCondition` for $(c,\varepsilon)$: a predicate on rigidified line bundles on $C \times_R T$ (for varying $R$-schemes $T$) which holds for the unit bundle, depends only on the isomorphism class of the underlying module, is stable under pullback along morphisms over $\operatorname{Spec} R$, and is moreover stable under tensor product and satisfies the cancellation clause that if the tensor product of $L$ and $M$ has trivial underlying module and $L$ satisfies $P$ then so does $M$. Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the $P$-part of the relative Picard functor: $h$ provides a rigidified line bundle `poincare` on $C \times_R D$ satisfying $P$, the universal property that every $M$ satisfying $P$ over an $R$-scheme $T$ is the pullback of `poincare` along a unique morphism $T \to D$ over $\operatorname{Spec} R$ (uniqueness up to isomorphism of underlying modules), and a trivialisation of the pullback of `poincare` along the zero section. Let $T$ be an object of the category of schemes over $\operatorname{Spec} R$. Endow $D$, viewed as an object over $\operatorname{Spec} R$, with the group-object structure `h.grpObj` transported from the commutative-group-valued presheaf of $P$-classes of rigidified line bundles through the representability isomorphism, so that the identity element $1$ of $\operatorname{Hom}_{\operatorname{Spec} R}(T, D)$ is defined. Then the pullback of `poincare` along the underlying morphism of schemes of $1$, which commutes with the structure morphisms, has underlying module isomorphic to the underlying module of the unit rigidified line bundle over $T.\mathrm{hom}$, namely the structure sheaf of $C \times_R T$; the assertion is the nonemptiness of the type of such isomorphisms, with no compatibility with the rigidifications claimed.
--
--   This is the statement that the Poincaré bundle restricted to the unit point of the representing group scheme is trivial, the geometric shadow of the fact that the representability isomorphism is an isomorphism of groups. It is used in the construction of the relative $\operatorname{Pic}^0$ as a group scheme, in particular in the companion statement about pullback along powers of a point and in the identification of the points of $\operatorname{Pic}^0$ for curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (T : Over (Spec (CommRingCat.of R))) :
    letI := h.grpObj
    Nonempty ((h.poincare.pullbackAlong
        ⟨(1 : T ⟶ Over.mk D.toBase).left, Over.w (1 : T ⟶ Over.mk D.toBase)⟩).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) T.hom).L) := by sorry
