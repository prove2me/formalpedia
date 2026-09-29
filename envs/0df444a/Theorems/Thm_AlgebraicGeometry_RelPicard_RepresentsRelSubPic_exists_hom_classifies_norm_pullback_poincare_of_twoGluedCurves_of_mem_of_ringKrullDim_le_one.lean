-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/04facdb0-0f43-54ea-9a60-719245236f83
-- title:
--   Norm–pullback endomorphism of the relative Pic⁰ over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring, let $c : C \to \operatorname{Spec} R$ be proper with $C$ integral and locally Noetherian and all stalks of $C$ integrally closed, and let $\varepsilon$ be a section of $c$. Assume `hsf`: for every algebraically closed field $k$ and every ring homomorphism $f : R \to k$ with non-zero kernel, the fibre $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ is reduced and is the set-theoretic union of the images of two closed immersions $i_1, i_2$ of proper smooth (relative dimension $1$) geometrically integral $k$-curves $C_1, C_2$, each carrying two affine opens that cover it with affine intersection, with $C_1 \times_{\text{fibre}} C_2$ reduced of finite cardinality $n > 0$. Let $\pi_1, \pi_2 : C' \to C$ be morphisms over $\operatorname{Spec} R$ with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$, a structure morphism $P \to \operatorname{Spec} R$ that is flat and locally of finite type, and a zero section, and let `hD` equip it with a rigidified line bundle (the Poincaré bundle) on $C \times_R P$ representing the subfunctor of $\varepsilon$-rigidified line bundles whose restrictions to geometric fibres are algebraically equivalent to zero, trivial along the zero section. Assume $C' \times_R P$ and $C \times_R P$ are integral with $C \times_R P$ having integrally closed sections on affine opens, and likewise over $P \times_R P$ (via the first projection followed by $P \to \operatorname{Spec} R$). Let $\mathrm{Nm}$ assign to a morphism of schemes a map on sheaves of modules satisfying `hNm`: for finite surjective $\pi : X \to Y$ between integral schemes with $Y$ normal on affine opens, $\mathrm{Nm}$ preserves invertibility and isomorphism classes of invertible sheaves, is multiplicative for tensor products of invertible sheaves, sends the unit to the unit, commutes with flat base change along pullback squares with normal integral target, and over an open $V \subseteq Y$ on which $\pi$ is flat, locally of finite presentation and of constant fibre rank $d$ agrees with `Scheme.Modules.normModule`, namely $\det^d \pi_* L \otimes (\det^d \pi_* \mathcal{O}_X)^\vee$. Finally let $V \subseteq C$ be open and $d : \mathbb{N}$ with $\pi_2$ restricted over $V$ flat, locally of finite presentation and of fibre rank $d$ everywhere on $V$, where $V$ contains every point whose local ring has Krull dimension at most $1$ and every point lying over the generic point of $\operatorname{Spec} R$. Then there is an endomorphism $T$ of $P$ over $\operatorname{Spec} R$ such that the pull-back of the Poincaré bundle along the base change of $T$ is isomorphic to the rigidification along the section `rigSection` of $\mathrm{Nm}_{\pi_2 \times \mathrm{id}_P}\bigl((\pi_1 \times \mathrm{id}_P)^* \mathcal{P}\bigr)$, such that $T$ is a homomorphism for the relative group law supplied by `hD` on points with values in any $R$-scheme, and such that the zero section followed by $T$ is again the zero section.
--
--   This is the construction of the action of a finite correspondence $C' \rightrightarrows C$ on the relative $\mathrm{Pic}^0$-object of a curve with semistable (two glued components) closed fibre over a discrete valuation ring, realised by norm along one leg of the pull-back along the other, in the style of the Albanese action used for Hecke operators. It is the generic form invoked to produce Hecke operators on the two-chart integral models of modular curves, and is cited by the constructions of the Hecke operators on the model of $X_1$ at $p$ and on the Hecke degeneracy pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one

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

    (V : C.Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V)
    (hVgen : ∀ x : C, (c.base x).asIdeal = ⊥ → x ∈ V) :
    ∃ Tℓ : SchemeHomOver D.toBase D.toBase,
      Nonempty ((hD.poincare.pullbackAlong Tℓ).L ≅
        Scheme.Modules.rigidify (rigSection c D.toBase ε) (pullback.snd c D.toBase)
          (Nm (curveChange π₂.1 π₂.2 D.toBase)
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) Tℓ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
            (NeronModelInfra.schemeHomOverComp x Tℓ) (NeronModelInfra.schemeHomOverComp y Tℓ)) ∧
      D.zeroSection ≫ Tℓ.1 = D.zeroSection := by sorry
