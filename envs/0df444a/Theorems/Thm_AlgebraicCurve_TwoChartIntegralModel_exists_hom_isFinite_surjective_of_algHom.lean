-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/7eae1958-996d-5d3d-9db6-441f915ba6fb
-- title:
--   Functoriality and finiteness of the two-chart integral model
-- statement:
--   Let $R$ be a commutative ring and let $F$, $F'$ be fields that are $R$-algebras, with $F'$ of characteristic zero. Let $\varphi : F \to F'$ be an $R$-algebra homomorphism whose underlying ring homomorphism is finite, i.e. $F'$ is a finite $F$-module via $\varphi$. Let $j \in F$ and $j' \in F'$ be non-zero with $\varphi(j) = j'$. Assume that the $R$-subalgebra $\mathrm{chartAlgFin}\,R\,F\,j$ of $F$ consisting of the elements of $F$ integral over $R[j] = \mathrm{Algebra.adjoin}\,R\,\{j\}$ is a Noetherian ring with $F$ as its fraction field, and likewise that $\mathrm{chartAlgInf}\,R\,F\,j$, the elements of $F$ integral over $R[j^{-1}]$, is Noetherian with fraction field $F$. Then there exist a morphism of schemes $m$ from `TwoChartIntegralModel R F' j'` to `TwoChartIntegralModel R F j` (each model being the pushout of the two chart schemes $\operatorname{Spec}$ of the finite and the infinite chart algebra along the corresponding overlap scheme) and $R$-algebra maps $\iota_F : \mathrm{chartAlgFin}\,R\,F\,j \to \mathrm{chartAlgFin}\,R\,F'\,j'$ and $\iota_I : \mathrm{chartAlgInf}\,R\,F\,j \to \mathrm{chartAlgInf}\,R\,F'\,j'$ such that: both $\iota_F$ and $\iota_I$ are given on elements by $\varphi$; $m$ followed by `toBase R F j` equals `toBase R F' j'`, so $m$ is a morphism over $\operatorname{Spec} R$; $\operatorname{Spec}(\iota_F)$ followed by the chart morphism `ιFin R F j` equals `ιFin R F' j'` followed by $m$, and similarly for $\iota_I$ and `ιInf`; the preimage under $m$ of the open range of `ιFin R F j` is the open range of `ιFin R F' j'`, and likewise for the infinite charts; and $m$ is a finite morphism whose map on underlying topological spaces is surjective.
--
--   This is the functoriality of the two-chart integral model along a finite extension of function fields: normalisation in a finite extension produces a finite surjective morphism of models that is pinned on both the finite and the infinite chart, and is compatible with the structure morphisms to $\operatorname{Spec} R$. It is used to construct degeneracy morphisms between Igusa-type integral models of modular curves and the comparison morphisms for the $q$-expansion function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_of_algHom
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [CharZero F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (hφ : φ.toRingHom.Finite)
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j')
    (hFfin : IsNoetherianRing ↥(chartAlgFin R F j) ∧ IsFractionRing ↥(chartAlgFin R F j) F)
    (hFinf : IsNoetherianRing ↥(chartAlgInf R F j) ∧ IsFractionRing ↥(chartAlgInf R F j) F) :
    ∃ (m : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (ιF : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'))
      (ιI : ↥(chartAlgInf R F j) →ₐ[R] ↥(chartAlgInf R F' j')),
      (∀ x, (ιF x : F') = φ x) ∧ (∀ x, (ιI x : F') = φ x) ∧
      m ≫ toBase R F j = toBase R F' j' ∧
      Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ m ∧
      Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ m ∧
      m ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F' j').opensRange ∧
      m ⁻¹ᵁ (ιInf R F j).opensRange = (ιInf R F' j').opensRange ∧
      IsFinite m ∧ Function.Surjective m.base := by sorry
