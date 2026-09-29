-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_of_isLocalization
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isPullback_toBase_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/25248e66-8a04-5e68-bde2-fe2f2c15e091
-- title:
--   Two-chart integral model and localisation of the base
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ a nonzero element. Let $R'$ be a commutative ring which is an $R$-algebra and for which $F$ is an $R'$-algebra, compatibly with the tower $R \to R' \to F$, and suppose $R'$ is a localisation of $R$ at a submonoid $M \subseteq R$. Write $\mathcal{X}_R =$ `TwoChartIntegralModel R F j` for the scheme obtained as the pushout of the two morphisms of spectra coming from the inclusions of the middle chart ring into the chart algebras $\mathrm{chartAlg}\,R\,F\,\{j\}$ and $\mathrm{chartAlg}\,R\,F\,\{j^{-1}\}$, where $\mathrm{chartAlg}\,R\,F\,S$ denotes the $R$-subalgebra of $F$ of elements integral over $R[S]$; let `ιFin R F j` and `ιInf R F j` be the two canonical morphisms from the spectra of these chart algebras into $\mathcal{X}_R$, and let `toBase R F j` $\colon \mathcal{X}_R \to \operatorname{Spec} R$ be the morphism descended from the structure maps of the two charts. The assertion is that there is a morphism $u \colon \mathcal{X}_{R'} \to \mathcal{X}_R$ such that, on each chart, `ιFin R' F j` followed by $u$ equals $\operatorname{Spec}$ of the inclusion $\mathrm{chartAlg}\,R\,F\,\{j\} \to \mathrm{chartAlg}\,R'\,F\,\{j\}$ followed by `ιFin R F j`, and likewise for the chart at $\{j^{-1}\}$ with `ιInf`, and such that the square with top edge $u$, left edge `toBase R' F j`, right edge `toBase R F j` and bottom edge $\operatorname{Spec}$ of $R \to R'$ is cartesian; that is, $\mathcal{X}_{R'} \cong \mathcal{X}_R \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ via $(u, \mathrm{toBase})$.
--
--   This is the statement that forming the two-chart integral model (gluing the integral closures of $R[j]$ and $R[j^{-1}]$ in $F$) commutes with localisation of the base ring, packaged as a cartesian square together with the chartwise comparison maps that pin $u$ down. It is used in the construction of the integral Igusa scheme, where the model over $\mathbb{Z}$ or over a localisation of it is compared with the model over $\mathbb{Q}$ and with fibre products formed elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_of_isLocalization.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isPullback_toBase_of_isLocalization
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] :
    ∃ u : AlgebraicCurve.TwoChartIntegralModel R' F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j,
      AlgebraicCurve.TwoChartIntegralModel.ιFin R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιFin R F j ∧
      AlgebraicCurve.TwoChartIntegralModel.ιInf R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιInf R F j ∧
      IsPullback u (AlgebraicCurve.TwoChartIntegralModel.toBase R' F j)
        (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by sorry
