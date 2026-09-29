-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_finite_faithfullyFlat_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/7d7e8849-acc1-5c82-8c5d-60059698a40f
-- title:
--   Descent of rigidified line bundles along finite flat base change
-- statement:
--   Let $R$ be a commutative ring, $c \colon C \to \operatorname{Spec} R$ a morphism of schemes and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume that for every $R$-algebra $A$ the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \mathcal{O})$, for the $R$-algebra structure on global sections coming from the projection to $\operatorname{Spec} A$, is bijective. Let $R'$ be an $R$-algebra that is finite and faithfully flat as an $R$-module, let $t \colon T \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, and let $T' = T \times_{\operatorname{Spec} R} \operatorname{Spec} R'$, regarded over $\operatorname{Spec} R$ through its second projection followed by $\operatorname{Spec} R' \to \operatorname{Spec} R$. Let $M'$ be a rigidified line bundle on $C \times_{\operatorname{Spec} R} T'$, that is, an invertible module $M'.L$ on this pullback together with a trivialisation of its restriction along the section of the projection determined by $\varepsilon$. Assume that for every scheme $Z$ over $\operatorname{Spec} R$ and every pair $p_1, p_2 \colon Z \to T'$ of morphisms over $\operatorname{Spec} R$ agreeing after composition with the projection $T' \to T$, the underlying invertible modules of the base changes $p_1^* M'$ and $p_2^* M'$ are isomorphic. Then there exists a rigidified line bundle $M$ on $C \times_{\operatorname{Spec} R} T$ whose base change along the projection $T' \to T$ has underlying module isomorphic to $M'.L$. The asserted isomorphism is one of invertible modules only; no compatibility with the rigidifications is claimed.
--
--   This is the existence half of the statement that the rigidified relative Picard functor of $c$ is a sheaf for the finite faithfully flat base change $\operatorname{Spec} R' \to \operatorname{Spec} R$, in the form used in the theory of Néron models. It is the input to the verification of the sheaf condition for the relative Picard presheaf cut out by the rigidification, [`AlgebraicGeometry.RelPicard.isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_finite_faithfullyFlat_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M' : RigidifiedLineBundle c ε (pullback.snd t (specMap R R') ≫ specMap R R'))
    (hM' : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd t (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst t (specMap R R') = p₂.1 ≫ pullback.fst t (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L)) :
    ∃ M : RigidifiedLineBundle c ε t,
      Nonempty ((M.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅ M'.L) := by sorry
