-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/71b6a0a6-edcd-5445-bebe-13732a42fcbd
-- title:
--   Positive-degree divisor bounding chart sections of the two-chart model
-- statement:
--   Let $R$ be a discrete valuation domain with $\mathfrak{m}_R=(\varpi)$, let $K_0$ be a fraction field of $R$, and let $F$ be a field that is an algebra over both $R$ and $K_0$ compatibly, such that `IsCurveOver K₀ F` holds: every nonzero element of $F$ has a principal divisor of degree $0$, every place of $F/K_0$ (a proper principal valuation subring of $F$ containing $K_0$) has residue field finite over $K_0$, and $\Omega_{F/K_0}$ is free of rank $1$ over $F$. Let $f\in F$ be nonzero and transcendental over $R$, with $F$ finite-dimensional and separable over $K_0(f)$. Write $A=$ `chartAlgFin R F f` for the subalgebra of elements of $F$ integral over $R[f]$, and let $\iota$ be a finite nonempty index type. For each $i$ let $\mathfrak{m}_i\subseteq A$ be a maximal ideal containing $\varpi$ and containing $f$ (as the element `jChartFin R F f` of $A$), and let $I_i\subseteq A$ be an ideal whose members are exactly those $a\in A$ for which $sa\in fA$ for some $s\notin\mathfrak{m}_i$; assume each $I_i\neq A$, each quotient $A/I_i$ is $\varpi$-torsion-free, and every prime of $A$ containing $I_i$ is contained in $\mathfrak{m}_i$. Then there is a divisor $D_K$ of $F/K_0$ (a finitely supported $\mathbb{Z}$-valued function on places) with $D_K\geq 0$, $\deg D_K>0$, and $D_K(v)=0$ whenever $f^{-1}$ lies in the valuation subring of $v$, such that for every $n\in\mathbb{N}$: (i) every $g$ in the Riemann–Roch space $L_{S_0}(nD_K)$, where $S_0=\{v: f\in\mathcal{O}_v\}$ and membership means $v(g)\leq \exp(nD_K(v))$ for all $v\in S_0$, admits $k\in\mathbb{N}$ with $\varpi^k g a\in A$ for all $a\in(\prod_i I_i)^n$; (ii) every element of `chartAlgMid R F f`, the elements of $F$ integral over $R[f,f^{-1}]$, lies in $L_{S_0\cap S_1}(nD_K)$, where $S_1=\{v: f^{-1}\in\mathcal{O}_v\}$; (iii) every $g\in L_{S_1}(nD_K)$ satisfies $\varpi^k g\in$ `chartAlgInf R F f`, the elements of $F$ integral over $R[f^{-1}]$, for some $k\in\mathbb{N}$.
--
--   This is the generic-fibre dictionary for the two-chart integral model attached to a coordinate $f$: it produces a single effective divisor of positive degree on the curve $F/K_0$, supported away from the places where $f^{-1}$ is regular, whose Riemann–Roch spaces sandwich the chart algebras and the inverses of the powers of the branch ideal $\prod_i I_i$. It feeds the localisation statement [`AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData), and through it the vanishing of the relevant $H^1$ up to $\varpi$-power torsion for large $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] [IsCurveOver K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i) (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hne : ∀ i, I i ≠ ⊤)
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i) :
    ∃ D_K : Divisor K₀ F, 0 ≤ D_K ∧ 0 < Divisor.degree D_K ∧
      (∀ v : Place K₀ F, f⁻¹ ∈ v.toValuationSubring → D_K v = 0) ∧
      ∀ n : ℕ,

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f),
            algebraMap R F ϖ ^ k * g * (a : F) = (b : F)) ∧

        (∀ z : ↥(chartAlgMid R F f), (z : F) ∈
          lSpaceOn ({v : Place K₀ F | f ∈ v.toValuationSubring} ∩ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring})
            ((n : ℤ) • D_K)) ∧

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ (k : ℕ) (b : ↥(chartAlgInf R F f)), algebraMap R F ϖ ^ k * g = (b : F)) := by sorry
