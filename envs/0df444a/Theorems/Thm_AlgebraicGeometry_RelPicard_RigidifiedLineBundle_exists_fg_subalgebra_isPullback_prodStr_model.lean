-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_fg_subalgebra_isPullback_prodStr_model
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_fg_subalgebra_isPullback_prodStr_model
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/67cf6bf4-632b-5a73-918b-ea29210757c3
-- title:
--   Cube datum descends to a finitely generated subring
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism carrying a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points of $f$, with the group axioms and compatibility under base change along $T'\to T$), and assume the predicate `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $M$ be a rigidified line bundle on the triple product, i.e. on the fibre product of $\operatorname{prodStr} f\,f=\mathrm{pr}_1\circ f\colon A\times_S A\to\operatorname{Spec}S$ with $f$: an invertible module $M.L$ on $(A\times_S A)\times_S A$ together with a trivialisation of its pullback along the section $\mathrm{rigSection}$ attached to the unit $(e,e)$ of the product law $L\times L$. The assertion is the existence of a finitely generated $\mathbb Z$-subalgebra $S_1\subseteq S$, a scheme $A_1$ with $f_1\colon A_1\to\operatorname{Spec}S_1$, a relative group law $L_1$ on $f_1$ that is commutative, the property bundle for $f_1$, and a morphism $a\colon A\to A_1$ making the square with $f$, $f_1$ and $\operatorname{Spec}$ of the inclusion $S_1\hookrightarrow S$ cartesian, such that $a$ transports multiplication: for every $T$, every $t\colon T\to\operatorname{Spec}S$ and all $T$-points $P,Q$ of $f$ over $t$, $(L.\mathrm{mul}\,t\,P\,Q)\circ a$ equals $L_1.\mathrm{mul}$ of $P\circ a$ and $Q\circ a$ over the composed base point; and finally a rigidified line bundle $M_1$ on $(A_1\times_{S_1}A_1)\times_{S_1}A_1$, rigidified along the unit of $L_1\times L_1$, such that $M.L$ is isomorphic to the pullback of $M_1.L$ along the morphism $(a\times a)\times a$ assembled from $a$ by the two universal properties. Only an isomorphism of the underlying invertible modules is asserted; no compatibility with the two rigidifications is required.
--
--   This is the Noetherian-approximation step for the theorem-of-the-cube datum: an abelian scheme with its group law and a rigidified line bundle on its triple relative product all descend to a finitely generated base, over which one may argue with Noetherian hypotheses. It is used by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_fg_subalgebra_isPullback_prodStr_model.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_fg_subalgebra_isPullback_prodStr_model
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f) :
    ∃ (S₁ : Subalgebra ℤ S) (_ : S₁.FG)
      (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (_ : L₁.IsCommutative) (_ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (_ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁)))) f₁),
      Nonempty (M.L ≅ (Scheme.Modules.pullback
        (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            show (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L) := by sorry
