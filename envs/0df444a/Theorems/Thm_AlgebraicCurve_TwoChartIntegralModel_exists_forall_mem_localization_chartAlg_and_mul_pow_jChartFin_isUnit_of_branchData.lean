-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/d615d1f3-58e1-57f4-ac7c-67c11672cf58
-- title:
--   Function with exact pole order along coordinate branches
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, $\varpi \in R$ with $\mathfrak m_R = (\varpi)$, $K_0$ a fraction field of $R$, and $F$ a field containing $K_0$ compatibly over $R$; let $f \in F$ be nonzero and transcendental over $R$, with $F$ finite-dimensional and separable over $K_0(f) = K_0(\{f\})$. Write $A =$ `chartAlgFin R F f` for the subalgebra of elements of $F$ integral over $R[f]$ and $A' =$ `chartAlgInf R F f` for those integral over $R[f^{-1}]$. Let $\iota$ be a finite index type and $\mathfrak m : \iota \to \mathrm{Ideal}\,A$ an injective family of maximal ideals, each containing the image of $\varpi$ and containing $f$ (as the element `jChartFin R F f`). Let $I_i \subseteq A$ satisfy $a \in I_i \iff \exists s \notin \mathfrak m_i,\ sa \in (f)$; assume each $A/I_i$ is a finite $R$-module on which multiplication by $\varpi$ is injective, every prime $P \supseteq I_i$ satisfies $P \subseteq \mathfrak m_i$, and every prime $P$ with $f, \varpi \in P$ and $P \subseteq \mathfrak m_i$ equals $\mathfrak m_i$. Then there are $n \ge 1$ and $g \in F$ with: $g \in A_{\mathfrak p}$ (i.e. $gc = b$ for some $b, c \in A$, $c \notin \mathfrak p$) for every prime $\mathfrak p$ of $A$ containing no $I_i$; $g \in A'_{\mathfrak p'}$ for every prime $\mathfrak p'$ of $A'$ containing $f^{-1}$ (the element `jInvChartInf R F f`); and for each $i$, $g f^n c = b$ with $b, c \in A \setminus \mathfrak m_i$, so that $g f^n$ is a unit in $A_{\mathfrak m_i}$.
--
--   This is the construction, on the two-chart integral model attached to $F/R[f]$, of a rational function regular away from the given branch data and with pole of exact order $n$ along each branch $\mathfrak m_i$ of $f = 0$; it is the case of the general branch-cutting statement in which each branch equation is taken to be the coordinate $f$ itself. It is used in the analysis of transcendental elements over Gauss valuations on Henselian local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (hinj : Function.Injective 𝔪)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i)
    (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hfin : ∀ i, Module.Finite R (↥(chartAlgFin R F f) ⧸ I i))
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)
    (hisol : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → jChartFin R F f ∈ P →
      algebraMap R ↥(chartAlgFin R F f) ϖ ∈ P → P ≤ 𝔪 i → P = 𝔪 i) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (g : F),
      (∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
        ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F)) ∧
      (∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
        ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F)) ∧
      (∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * f ^ n * (c : F) = (b : F)) := by sorry
