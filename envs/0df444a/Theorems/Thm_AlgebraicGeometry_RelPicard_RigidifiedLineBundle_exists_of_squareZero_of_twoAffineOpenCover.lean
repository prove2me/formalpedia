-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/282bc917-e984-525f-9001-850443da89d1
-- title:
--   Rigidified line bundles lift along square-zero base extensions
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme with a morphism $c \colon C \to \operatorname{Spec} R$, and let $\varepsilon$ be a morphism $\operatorname{Spec} R \to C$ with $\varepsilon$ followed by $c$ equal to the identity, i.e. a section of $c$. Let $\mathcal{V}$ be a two-affine open cover of $C$: two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and with $U_0 \sqcap U_1$ affine. Let $B$ be an $R$-algebra and $I \subseteq B$ an ideal with $I^2 = \bot$, and let $\iota$ be a morphism $\operatorname{Spec}(B/I) \to \operatorname{Spec} B$ commuting with the structure morphisms to $\operatorname{Spec} R$ whose underlying morphism is $\operatorname{Spec}$ of the quotient map $B \to B/I$. Let $M$ be a rigidified line bundle on $C$ relative to $R$ over the base $\operatorname{Spec}(B/I)$, that is: a module $M.L$ on the fibre product of $c$ with $\operatorname{Spec}(B/I) \to \operatorname{Spec} R$ which is invertible (each point has an open neighbourhood on which the restriction of $M.L$ is isomorphic to the unit sheaf of modules), together with an isomorphism between the pullback of $M.L$ along the rigidifying section $\operatorname{Spec}(B/I) \to C \times_{\operatorname{Spec} R} \operatorname{Spec}(B/I)$ determined by $\varepsilon$ and the unit sheaf. Then there exists a rigidified line bundle $M'$ on $C$ relative to $R$ over the base $\operatorname{Spec} B$ whose pullback along $\iota$ has underlying module isomorphic to $M.L$. Only an isomorphism of the underlying modules is asserted, with no compatibility with the rigidifications.
--
--   This is the lifting step expressing formal smoothness of the rigidified relative Picard functor of $C$ over $R$, in the case where $C$ admits a cover by two affine opens with affine intersection (the situation of a relative curve with a section, where the obstruction to lifting would lie in a vanishing second cohomology group). It is used in the proofs that the functor representing the relevant relative Picard subfunctor is smooth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))) :
    ∃ M' : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R B))),
      Nonempty ((M'.pullbackAlong ι).L ≅ M.L) := by sorry
