-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/1fd32d58-9c0f-56e1-91b3-8a2d99294e7e
-- title:
--   Primitivity of the rigidified norm of the Poincaré bundle
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$, let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite equal to the identity), and let $\pi_1,\pi_2 : C' \to C$ be morphisms over $\operatorname{Spec} R$ with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$ with a structure morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$, and let $hD$ witness that $D$ represents the subfunctor of the $\varepsilon$-rigidified relative Picard functor of $c$ cut out by the condition `FibrewiseAlgEquivZero` (the cut `algEquivZeroCut c ε`): it provides a Poincaré rigidified line bundle $hD.\mathrm{poincare}$ on $C \times_R P$, membership of that bundle in the cut, the universal property classifying rigidified bundles satisfying the cut by a unique $P$-point, and triviality along the zero section. Assume $C' \times_R P$ and $C \times_R P$ are integral, $C \times_R P$ is normal (sections over each affine open are integrally closed), $D.\mathrm{toBase}$ is flat and locally of finite type, and likewise $C' \times_R (P \times_R P)$ and $C \times_R (P \times_R P)$ are integral with $C \times_R (P \times_R P)$ normal. Let $\mathrm{Nm}$ assign to each morphism $\pi : X \to Y$ of schemes a map from $X$-modules to $Y$-modules, subject to the hypothesis $h\mathrm{Nm}$: for every finite surjective $\pi : X \to Y$ with $X$, $Y$ integral and $Y$ normal, $\mathrm{Nm}_\pi$ preserves invertibility, sends isomorphic invertible modules to isomorphic modules, is multiplicative for tensor products of invertible modules, carries the unit to the unit, commutes with flat base change along any pullback square $g' , \pi' , \pi , g$ with $g$ flat and the new source and target integral, the new target normal, and, over any open $V \subseteq Y$ on which $\pi$ is flat, locally of finite presentation and of constant fibre rank $d$, restricts to $\det_d$ of the pushforward of the restricted module tensored with the dual of $\det_d$ of the pushforward of the unit. Write $\Lambda$ for $\mathrm{Nm}$ along the base change of $\pi_2$ to $C' \times_R P \to C \times_R P$ applied to the pullback of the Poincaré module along the base change of $\pi_1$, and assume $\Lambda$ is invertible ($h\mathrm{inv}$); let $M'$ be the rigidification $\Lambda \otimes q^{*}\mathrm{dual}(\sigma^{*}\Lambda)$ of $\Lambda$ along the $\varepsilon$-section. Then for every scheme $T$ with $s : T \to \operatorname{Spec} R$ and all $T$-points $x,y$ of $P$ over $\operatorname{Spec} R$, the module underlying the pullback of $M'$ along the product $x \cdot y$ formed with the relative group law on $D$ coming from $hD$ and the group cut `algEquivZeroGroupCut` is isomorphic to the tensor product of the modules underlying the pullbacks of $M'$ along $x$ and along $y$; the conclusion asserts nonemptiness of the type of such isomorphisms.
--
--   This is the primitivity (cube-type) property of the line bundle obtained from the Poincaré bundle of a relative $\mathrm{Pic}^0$ by pulling back along one leg of a finite correspondence and taking the norm along the other: it says that the associated map on $T$-points is compatible with the group law. It is used to produce, from such a correspondence, a morphism of relative Jacobians classifying the normed transform, which in turn feeds the construction of Hecke operators on the relevant modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare

    (R : Type) [CommRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))

    [Flat D.toBase] [LocallyOfFiniteType D.toBase]
    [IsIntegral ↑(pullback c' (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    [IsIntegral ↑(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    (hnorm₂ : ∀ U : (pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase), U))

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
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y)).L ≅
      (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong x).tensor
        ((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong y)).L) := by sorry
