-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
-- name    : AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/782530d0-83a1-55fc-9fb9-57d91466159b
-- title:
--   Gauss-point valuations of g are the A_{mathfrak q_i}
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, $\varpi\in R$ a generator of its maximal ideal, $K_0$ a fraction field of $R$, and $F$ a field equipped with compatible $R$- and $K_0$-algebra structures. Let $f\in F$ be nonzero and transcendental over $R$, with $F$ finite-dimensional and separable over the intermediate field $K_0(f)=$ `IntermediateField.adjoin K₀ {f}`. Write $A=$ `chartAlgFin R F f` for the subalgebra of elements of $F$ integral over $R[f]$ and $A'=$ `chartAlgInf R F f` for the elements integral over $R[f^{-1}]$, and let `jInvChartInf R F f` denote $f^{-1}$ as an element of $A'$. Let $\iota$ be a finite index type and, for each $i$, let $\mathfrak q_i$ be a minimal prime over $\varpi A$, $\mathfrak m_i$ a maximal ideal of $A$ containing $\mathfrak q_i$ such that $\mathfrak q_i$ is the only minimal prime over $\varpi A$ contained in $\mathfrak m_i$, let $t_i\in\mathfrak m_i\setminus\mathfrak q_i$, and let $I_i$ be an ideal containing $t_i$ all of whose prime divisors are contained in $\mathfrak m_i$. Let $n\ge 1$ and $g\in F$ satisfy: $g\in A_{\mathfrak p}$ for every prime $\mathfrak p$ of $A$ with $I_i\not\subseteq\mathfrak p$ for all $i$ (expressed as $g c=b$ for some $b,c\in A$, $c\notin\mathfrak p$); $g\in A'_{\mathfrak p'}$ for every prime $\mathfrak p'$ of $A'$ containing $f^{-1}$; and, for each $i$, $g\,t_i^{\,n}$ is a unit of $A_{\mathfrak m_i}$, i.e. $g t_i^{\,n} c=b$ with $b,c\in A\setminus\mathfrak m_i$. The conclusion has two parts: if $\iota$ is nonempty then $g$ is transcendental over $R$; and for every valuation subring $O$ of $F$ containing the image of $R$ and in which the image of $\varpi$ is a nonunit, the condition that $P(g)$ and $P(g)^{-1}$ both lie in $O$ for every $P\in R[X]$ not divisible by the constant $\varpi$ holds if and only if there is an index $i$ with $O=A_{\mathfrak q_i}$, in the sense that $y\in O$ precisely when $yc=b$ for some $b,c\in A$ with $c\notin\mathfrak q_i$.
--
--   The left-hand condition says that $O$ lies over the Gauss point of the $g$-line, i.e. $g\in O$ with residue transcendental over the residue field of $R$; the statement thus identifies the vertical components of the special fibre of the two-chart integral model on which $g$ is non-constant as exactly those indexed by $\iota$, $g$ having a pole of order at least one along each of the chosen branches and being regular elsewhere. It is used in the construction of transcendental functions with prescribed Gauss-point behaviour over a Henselian base, via [`ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing`](thm.html#ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔮 : ι → Ideal ↥(chartAlgFin R F f))
    (h𝔮 : ∀ i, 𝔮 i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes)
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (h𝔮𝔪 : ∀ i, 𝔮 i ≤ 𝔪 i)
    (honly : ∀ i, ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 i → 𝔮' = 𝔮 i)

    (t : ι → ↥(chartAlgFin R F f)) (ht : ∀ i, t i ∈ 𝔪 i) (ht𝔮 : ∀ i, t i ∉ 𝔮 i)
    (I : ι → Ideal ↥(chartAlgFin R F f)) (htI : ∀ i, t i ∈ I i)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)

    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (h1 : ∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
      ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F))
    (h2 : ∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
      ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F))
    (h3 : ∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * (t i : F) ^ n * (c : F) = (b : F)) :
    (Nonempty ι → Transcendental R g) ∧
    ∀ O : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ O) → algebraMap R F ϖ ∈ O.nonunits →
      ((∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) ↔
        ∃ i, ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) := by sorry
