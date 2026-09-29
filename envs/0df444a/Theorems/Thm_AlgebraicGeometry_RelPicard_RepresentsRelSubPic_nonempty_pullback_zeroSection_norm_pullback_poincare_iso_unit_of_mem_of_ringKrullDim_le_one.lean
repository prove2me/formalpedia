-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e6c14348-7057-5e56-8cef-7560c9e7525e
-- title:
--   Norm of the pulled-back Poincaré bundle is trivial along the zero section
-- statement:
--   Let $R$ be a local commutative ring, and let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be morphisms of schemes with $C$ integral, locally Noetherian and with all stalks integrally closed; let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite equal to the identity), and let $\pi_1, \pi_2 : C' \to C$ be morphisms over $\operatorname{Spec} R$ with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$ with structure morphism $P \to \operatorname{Spec} R$ and a zero section, and let $hD$ exhibit $D$ as representing the $\varepsilon$-rigidified relative Picard condition `algEquivZeroCut` of $c$ (fibrewise algebraic equivalence to zero), with Poincaré bundle $\mathcal{P} = hD.poincare.L$ on $C \times_R P$: thus every rigidified invertible module on $C \times_R T$ satisfying the condition is, uniquely, the pullback of $\mathcal{P}$ along a map $T \to P$ over $\operatorname{Spec} R$, and the pullback of $\mathcal{P}$ along the zero section is the unit. Assume $C' \times_R P$ and $C \times_R P$ integral, all affine opens of $C \times_R P$ with integrally closed sections, and $P \to \operatorname{Spec} R$ locally of finite type. Let $\mathrm{Nm}$ assign to each morphism $X \to Y$ of schemes an operation $X.Modules \to Y.Modules$ satisfying, for every finite surjective $\pi : X \to Y$ with $X$, $Y$ integral and all affine opens of $Y$ having integrally closed sections: preservation of invertibility, invariance under isomorphism of the (invertible) argument, multiplicativity on tensor products of invertibles, triviality on the unit, compatibility with flat base change along pullback squares over integral bases whose affine opens have integrally closed sections, and agreement over an open $V \subseteq Y$, where $\pi$ is flat, locally of finite presentation and of constant fibre rank $d$, with $\mathrm{normModule}$, i.e. $\det_d$ of the pushforward tensored with the dual of $\det_d$ of the pushforward of the unit. Write $M := \mathrm{Nm}_{\pi_2 \times \mathrm{id}_P}\bigl((\pi_1 \times \mathrm{id}_P)^* \mathcal{P}\bigr)$ on $C \times_R P$ and assume $M$ invertible. Finally let $V \subseteq C$ be open and $d \in \mathbb{N}$ with $\pi_2$ over $V$ flat, locally of finite presentation and of fibre rank $d$ at every point of $V$, and with $V$ containing every $x \in C$ whose stalk has Krull dimension at most $1$. The conclusion is twofold: the pullback of $M$ along the morphism $C \times_R \operatorname{Spec} R \to C \times_R P$ induced by the zero section of $D$ is isomorphic to the unit module, and likewise the underlying module of the rigidified line bundle obtained by $\varepsilon$-rigidifying $M$ and pulling back along the zero section is isomorphic to the unit rigidified bundle's module.
--
--   This is the zero-section triviality check for the norm construction that transports the Poincaré bundle of a relative $\mathrm{Pic}^0$-designation along a pair of morphisms $\pi_1, \pi_2 : C' \to C$ with $\pi_2$ finite and surjective, the condition that allows the universal property of $D$ to be applied to the normed bundle. It is used, together with the companion membership statement for the fibrewise algebraic-equivalence condition, to produce the morphism on the relative Jacobian classifying a finite correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one

    (R : Type) [CommRing R] [IsLocalRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsIntegral C] [IsLocallyNoetherian C] (hCnorm : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))
    [LocallyOfFiniteType D.toBase]

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))

    (V : C.Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V) :

    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c
        (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase))).obj
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of R)))).ringCatSheaf) ∧

    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := ε)
        (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 _)).L) := by sorry
