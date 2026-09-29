-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
-- name    : AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/328e3cb8-60b1-5458-becf-b4da15fe165a
-- title:
--   Čech H¹ vanishing on two transversally glued curves
-- statement:
--   Let $k$ be an algebraically closed field, and let $x : X \to \operatorname{Spec} k$ be proper with $X$ reduced. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ equals $c_j$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$. Assume the scheme $N := C_1 \times_X C_2$ is reduced and that its underlying space has cardinality $n > 0$. Let $M$ be an $\mathcal{O}_X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the restriction of $M$ to $U$ isomorphic to the unit module, and fix two-chart affine open covers $\mathcal V_1$ of $C_1$ and $\mathcal V_2$ of $C_2$ (two affine opens with affine intersection whose union is everything). Write, for a two-chart cover, $H^0$ for the kernel and $H^1$ for the cokernel of the associated Čech differential, and for a morphism $f$ write $f.\mathrm{ker}$ for its ideal sheaf datum and $(f.\mathrm{ker}).\mathrm{module}$ for the corresponding ideal as an $\mathcal{O}$-module (the kernel of the unit map to the pushforward of the unit along the closed subscheme inclusion). The hypotheses are: (h1) over $\mathcal V_1$ the module $i_1^\ast M \otimes (\mathrm{pr}_1 : N \to C_1).\mathrm{ker}.\mathrm{module}$ has $\dim_k H^0 = 0$ and $H^1$ a subsingleton; (h2) over $\mathcal V_2$ the module $i_2^\ast M$ has $H^1$ a subsingleton and $\dim_k H^0 = 1$; (h3) for every section $p : \operatorname{Spec} k \to C_2$ of $c_2$ whose image in $X$ lies in the image of $i_1$, the module $i_2^\ast M \otimes (p.\mathrm{ker}).\mathrm{module}$ over $\mathcal V_2$ has $\dim_k H^0 = 0$. The conclusion is twofold: for every two-chart affine open cover $\mathcal V$ of $X$, the Čech $H^1$ of $M$ over $\mathcal V$ is a subsingleton; and for every nonzero global section $\sigma : \mathbf{1} \to M$, the support of the zero-scheme ideal of $\sigma$ (the infimum of the ideal sheaf data dominating the coefficient ideals of $\sigma$ on all affine opens) is contained in the complement of the image of $N \to C_1 \to X$.
--
--   This is the Mayer–Vietoris step for an invertible module on a curve obtained by gluing two smooth proper geometrically integral curves transversally along finitely many points: component-wise cohomological hypotheses on $C_1$ (twisted by the ideal of the crossings) and on $C_2$ force $\check H^1$ to vanish on the glued scheme and force any nonzero global section to be invertible at the crossings. It feeds the construction of split injections and support conditions for relative Picard data at a two-sided degenerate fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover)

    (h1 : Module.finrank k (𝒱₁.sectionsOf c₁
        ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H0 = 0 ∧
      Subsingleton (𝒱₁.sectionsOf c₁
        ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H1)

    (h2 : Subsingleton (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H1 ∧
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H0 = 1)

    (h3 : ∀ p : Spec (CommRingCat.of k) ⟶ C₂, p ≫ c₂ = 𝟙 _ →
      Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base →
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M ⊗ (p.ker).module)).H0 = 0) :
    (∀ 𝒱 : X.TwoAffineOpenCover, Subsingleton (𝒱.sectionsOf x M).H1) ∧
    ∀ σ : 𝟙_ X.Modules ⟶ M, σ ≠ 0 →
      ((Scheme.Modules.zeroSchemeIdeal σ).support : Set X) ⊆ (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ := by sorry
