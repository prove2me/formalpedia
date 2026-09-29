-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/9485cde4-2eb4-557d-ad6d-f82602c1b7d3
-- title:
--   Norm of the Poincaré bundle is fibrewise algebraically trivial
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), and let $c : C \to \operatorname{Spec} R$ be proper with $C$ integral, locally Noetherian and with all stalks integrally closed, equipped with a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Assume the hypothesis `hsf`: for every algebraically closed field $k$ and every ring homomorphism $f : R \to k$ with non-zero kernel, the fibre $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ is reduced and is the set-theoretic union of the images of two closed immersions $i_1, i_2$ into it from proper smooth (relative dimension $1$) geometrically integral curves $C_1, C_2$ over $k$, each carrying two affine opens which cover it and have affine intersection, such that $\operatorname{pullback} i_1\, i_2$ is reduced with $n > 0$ points. Let $c' : C' \to \operatorname{Spec} R$ and let $\pi_1, \pi_2 : C' \to C$ be morphisms over $R$ with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$ with structure morphism $P \to \operatorname{Spec} R$ and a zero section, and let `hD` exhibit $D$ as representing the condition `algEquivZeroCut`: a rigidified line bundle `hD.poincare` on $C \times_R P$ all of whose geometric fibres are algebraically equivalent to zero, universal among rigidified line bundles with this fibrewise property, and trivial along the zero section. Assume $C' \times_R P$ and $C \times_R P$ integral, the sections of $C \times_R P$ over affine opens integrally closed, and $P \to \operatorname{Spec} R$ locally of finite type. Let $\mathrm{Nm}$ assign to each morphism of schemes an operation on module objects, subject to `hNm`: for every finite surjective $\pi : X \to Y$ with $X, Y$ integral and $Y$ normal on affine opens, $\mathrm{Nm}_\pi$ preserves invertibility, respects isomorphism of invertible modules, is multiplicative for tensor products of invertibles, sends the unit to the unit, commutes with flat base change along pullback squares over integral normal targets, and agrees, after restriction to an open $V \subseteq Y$ over which $\pi$ is flat, locally of finite presentation of constant fibre rank $d$, with the determinant norm `Scheme.Modules.normModule`. Assume the module $M := \mathrm{Nm}_{\pi_2 \times_R P}\bigl((\pi_1 \times_R P)^{*}\,\mathcal{P}\bigr)$ on $C \times_R P$ is invertible, where $\mathcal{P}$ is the module underlying `hD.poincare` and $\pi_i \times_R P$ denotes `curveChange`. Finally let $V$ be an open of $C$ and $d$ a natural number such that $\pi_2$ restricted over $V$ is flat, locally of finite presentation and of fibre rank $d$ at every point of $V$, with $V$ containing every point of $C$ whose local ring has Krull dimension at most $1$ and every point lying over the zero ideal of $R$. Then the rigidified line bundle obtained from $M$ by `RigidifiedLineBundle.ofInvertible` (that is, $M$ tensored with the pullback along $C \times_R P \to P$ of the dual of its restriction along the rigidifying section) satisfies `FibrewiseAlgEquivZero`: for every algebraically closed field $k$ and every $k$-point $s$ of $P$, the pullback of its module to the fibre of $C \times_R P$ over $s$ is algebraically equivalent to zero.
--
--   This is the step showing that the correspondence transform of the Poincaré bundle by the pair $(\pi_1, \pi_2)$, normed along the finite surjective leg $\pi_2$, satisfies the $\mathrm{Pic}^0$ condition fibre by fibre over the representing base $P$ — the hypothesis needed before the universal property of $D$ can be invoked. It is used by [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one), which produces from it the classifying morphism, i.e. the endomorphism of the relative $\mathrm{Pic}^0$ attached to the correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one.lean

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
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one

    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [IsIntegral C] [IsLocallyNoetherian C] (hCnorm : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (hsf : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : R →+* k), RingHom.ker f ≠ ⊥ →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c (Spec.map (CommRingCat.ofHom f))))
        (i₂ : SchemeHomOver c₂ (pullback.snd c (Spec.map (CommRingCat.ofHom f))))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
        (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
        IsReduced (pullback c (Spec.map (CommRingCat.ofHom f))) ∧
        (∀ z : ↥(pullback c (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n)

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
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V)
    (hVgen : ∀ x : C, (c.base x).asIdeal = ⊥ → x ∈ V) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε)
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
      hinv) := by sorry
