-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
-- name    : AlgebraicCurve.TwoChartIntegralModel.forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/31c24768-3aa9-5762-b492-2cfb949bb1af
-- title:
--   Polynomials in a pole function are units of A_q
-- statement:
--   Let $R$ be a discrete valuation domain, $\varpi \in R$ an element generating its maximal ideal, $K_0$ a fraction field of $R$, and $F$ a field that is an algebra over $R$ and over $K_0$ compatibly; let $f \in F$ be nonzero, and write $A =$ `chartAlgFin R F f` for the subalgebra of $F$ of elements integral over $R[f] =$ `Algebra.adjoin R {f}`, i.e. the integral closure of $R[f]$ in $F$. Assume given: a prime ideal $\mathfrak q$ of $A$ with the image of $\varpi$ in $A$ lying in $\mathfrak q$; a maximal ideal $\mathfrak m$ of $A$ with $\mathfrak q \le \mathfrak m$; an element $t \in \mathfrak m$ with $t \notin \mathfrak q$; an integer $n \ge 1$; and $g \in F$ such that $g c = b$ for some $b, c \in A$ with $c \notin \mathfrak q$ (so $g$ lies in the localisation $A_{\mathfrak q}$ realised inside $F$), and $g t^{n} c = b$ for some $b, c \in A$ with $b \notin \mathfrak m$ and $c \notin \mathfrak m$ (so $g t^{n}$ is a unit of $A_{\mathfrak m}$ inside $F$). Let $O$ be a valuation subring of $F$ whose elements are exactly the $y \in F$ with $y c = b$ for some $b, c \in A$, $c \notin \mathfrak q$. Then for every polynomial $P \in R[X]$ that is not divisible by the constant polynomial $\varpi$, both $P(g) \in O$ and $P(g)^{-1} \in O$, inversion being taken in the field $F$ (where $0^{-1} = 0$).
--
--   This is the valuation-theoretic step saying that a function with a genuine pole of order $n \ge 1$ along the branch cut out by $t$ at $\mathfrak m$ takes, under every polynomial over $R$ with a coefficient that is a unit, a value which is a unit of the valuation ring attached to $\mathfrak q$; equivalently, $g$ lies over the Gauss point of the component corresponding to $\mathfrak q$ in the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236). It is used in the assembly [`AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization`](thm.html#AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)]
    (𝔮 : Ideal ↥(chartAlgFin R F f)) [𝔮.IsPrime] (hϖ𝔮 : algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔮)
    (𝔪 : Ideal ↥(chartAlgFin R F f)) (h𝔪 : 𝔪.IsMaximal) (h𝔮𝔪 : 𝔮 ≤ 𝔪)
    (t : ↥(chartAlgFin R F f)) (ht : t ∈ 𝔪) (ht𝔮 : t ∉ 𝔮)
    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (hg : ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ g * (c : F) = (b : F))
    (h3 : ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 ∧ c ∉ 𝔪 ∧ g * (t : F) ^ n * (c : F) = (b : F))
    (O : ValuationSubring F)
    (hO : ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ y * (c : F) = (b : F)) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O := by sorry
