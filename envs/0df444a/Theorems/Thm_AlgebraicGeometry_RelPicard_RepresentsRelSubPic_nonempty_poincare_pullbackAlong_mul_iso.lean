-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/03e26f33-8dc6-5aa7-8768-5c2dc93a376a
-- title:
--   Poincaré bundle pulled back along a product of points
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a scheme over $R$ and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $P$ be a condition on rigidified line bundles on the fibres $C \times_R T$ (a predicate containing the unit, stable under isomorphism of the underlying modules and under base change along morphisms over $\operatorname{Spec} R$) which in addition is stable under the tensor operation $(L,M) \mapsto L.L \otimes M.L$ and satisfies the cancellation clause: if $L \otimes M$ is isomorphic to the unit and $L$ lies in $P$, then so does $M$. Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase} \colon D \to \operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the $P$-part of the rigidified relative Picard functor: $h$ provides a rigidified line bundle $\mathcal P$ on $C \times_R D$ lying in $P$, the universal property that every $P$-bundle on $C\times_R T$ is the pullback of $\mathcal P$ along a unique morphism $T \to D$ over $\operatorname{Spec} R$ (up to isomorphism of underlying modules), and the normalisation that the pullback of $\mathcal P$ along the zero section is isomorphic to the unit. Give $D$, as an object of the category of schemes over $\operatorname{Spec} R$, the group-object structure `h.grpObj` obtained from this representability together with the commutative group structure on the $P$-Picard presheaf. Then for every object $T$ over $\operatorname{Spec} R$ and all morphisms $a, b \colon T \to D$ over $\operatorname{Spec} R$ there exists an isomorphism of sheaves of modules on $C \times_R T$
--   $$(\mathrm{id}_C \times (a\cdot b))^{*}\mathcal P \;\cong\; (\mathrm{id}_C \times a)^{*}\mathcal P \otimes (\mathrm{id}_C \times b)^{*}\mathcal P,$$
--   where $a \cdot b$ is the product under the group law of $D$; the assertion is the nonemptiness of the type of such isomorphisms, not a chosen one.
--
--   This is the statement that the group law on the scheme representing the $P$-part of the rigidified relative Picard functor is computed by tensor product of the corresponding pullbacks of the Poincaré bundle, in the unquotiented form of an isomorphism of the underlying modules rather than an equality of isomorphism classes. It is used throughout the construction of homomorphisms out of and into such Picard schemes, for instance in the analysis of tensor products of classified bundles and in the production of additive maps on points compatible with base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ Over.mk D.toBase) :
    letI := h.grpObj
    Nonempty ((h.poincare.pullbackAlong ⟨(a * b).left, Over.w (a * b)⟩).L ≅
      ((h.poincare.pullbackAlong ⟨a.left, Over.w a⟩).tensor (h.poincare.pullbackAlong ⟨b.left, Over.w b⟩)).L) := by sorry
