-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/626ca267-482f-522e-b245-a7e4b7532d65
-- title:
--   Descending the cube faces to a noetherian base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, equipped with a relative group law $L$ (functorial multiplication, unit and inverse on $S$-points satisfying the group axioms and compatible with base change) and with an `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, has connected fibres and admits a relative group law. Let $M$ be a rigidified line bundle on the threefold fibre product $(A\times_S A)\times_S A$, that is, an invertible module on it together with a trivialisation along the section determined by the unit of the product law $L\times L$. Hypotheses $h_1$, $h_2$, $h_3$ say that the pullbacks of $M.L$ along the three face embeddings $A\times_S A \to (A\times_S A)\times_S A$ given respectively by $(x,y)\mapsto((e,x),y)$, $(x,y)\mapsto((x,e),y)$ and $(x,y)\mapsto((x,y),e)$ are `LocIsoOnBase` to the unit module, meaning that every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. Assume further a finite-stage model: a finitely generated $\mathbb{Z}$-subalgebra $S_1\subseteq S$, a scheme $A_1$ with $f_1 : A_1 \to \operatorname{Spec} S_1$, a commutative relative group law $L_1$ on $f_1$ satisfying the same smooth–proper–connected-fibre bundle of properties, a morphism $a : A \to A_1$ making $f$ the base change of $f_1$ along $\operatorname{Spec}$ of the inclusion $S_1\hookrightarrow S$, compatibility of $a$ with the two multiplications on all $T$-points, a rigidified line bundle $M_1$ on $(A_1\times_{S_1}A_1)\times_{S_1}A_1$, and an isomorphism of $M.L$ with the pullback of $M_1.L$ along the induced map $(a\times a)\times a$. The conclusion asserts the existence of a noetherian commutative ring $S_0$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} S_0$, a relative group law $L_0$ on $f_0$ satisfying the same bundle of properties, and a rigidified line bundle $M_0$ on $(A_0\times_{S_0}A_0)\times_{S_0}A_0$, such that the three face pullbacks of $M_0.L$ are again locally isomorphic on $\operatorname{Spec} S_0$ to the unit module, and such that if $M_0.L$ is isomorphic to the underlying module of the unit rigidified line bundle over $S_0$ then $M.L$ is isomorphic to the underlying module of the unit rigidified line bundle over $S$. No comparison morphism between $S_0$ and $S$ is part of the conclusion: the two situations are linked only through this implication.
--
--   This is the noetherian-approximation step in the proof of the theorem of the cube over an arbitrary affine base: starting from a model of the data over a finitely generated subring, the three face trivialisations are pushed down to a noetherian stage, so that the triviality of the cube bundle may be proved there and transported back. It is used by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _))
    (S₁ : Subalgebra ℤ S) (hS₁ : S₁.FG)
      (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (hc₁ : L₁.IsCommutative) (hA₁ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁)))) f₁)
    (hM : Nonempty (M.L ≅ (Scheme.Modules.pullback
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
          ha.w.symm)).obj M₁.L)) :
    ∃ (S₀ : Type) (_ : CommRing S₀) (_ : IsNoetherianRing S₀) (A₀ : Scheme) (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀))
      (L₀ : RelativeGroupLaw S₀ f₀) (_ : AbelianSchemePropertyBundle S₀ f₀)
      (M₀ : RigidifiedLineBundle (prodStr f₀ f₀) ((L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀),
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (L₀.one (prodStr f₀ f₀)).1 (pullback.fst f₀ f₀) (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc, (L₀.one _).2]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst f₀ f₀) (L₀.one (prodStr f₀ f₀)).1 (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) (L₀.one (prodStr f₀ f₀)).1 (by rw [Category.id_comp, (L₀.one _).2]))).obj M₀.L) (𝟙_ _) ∧
      (Nonempty (M₀.L ≅ (RigidifiedLineBundle.unit (c := prodStr f₀ f₀) (ε := (L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀).L) →
        Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f).L)) := by sorry
