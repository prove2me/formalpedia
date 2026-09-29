-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
-- name    : AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/28bfde37-d4c5-570e-95ae-0f66402370fb
-- title:
--   Integrality of (1+j⁻¹a)j'⁻¹ gives the two-chart visibility condition
-- statement:
--   Let $R$ be a commutative ring and $F$ a field equipped with an $R$-algebra structure, and let $j, j' \in F$ be non-zero. For $x \in F$ non-zero write $A_\infty(x)$ for the subalgebra `chartAlgInf R F x` of $F$, namely the set of elements of $F$ integral over the $R$-subalgebra $\mathrm{Algebra.adjoin}\,R\,\{x^{-1}\} = R[x^{-1}] \subseteq F$ (so $A_\infty(x)$ is the integral closure of $R[x^{-1}]$ in $F$). Assume there exists $a \in R[j^{-1}]$ such that the element $(1 + j^{-1}a)\,j'^{-1}$ of $F$ is integral over $R[j^{-1}]$. The conclusion is that for every $y \in A_\infty(j')$ there is an $s \in A_\infty(j)$ such that, first, $s = 1 + j^{-1}a'$ for some $a' \in A_\infty(j)$ (note that $a'$ is only required to lie in the integral closure $A_\infty(j)$, not in $R[j^{-1}]$ itself), and second, $s\,y \in A_\infty(j)$.
--
--   This supplies the visibility hypothesis of the gluing statement for two-chart integral models of a common function field, in the shape in which the hypothesis is actually checked: one exhibits a single element $a$ of $R[j^{-1}]$ making $(1+j^{-1}a)j'^{-1}$ integral over $R[j^{-1}]$. It is used in the construction of the Atkin–Lehner involution on the integral model of the modular curve, via [`ModularCurve.IgusaScheme.exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd`](thm.html#ModularCurve.IgusaScheme.exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hb : ∃ a ∈ Algebra.adjoin R ({j⁻¹} : Set F),
      IsIntegral (Algebra.adjoin R ({j⁻¹} : Set F)) ((1 + j⁻¹ * a) * j'⁻¹)) :
    ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j := by sorry
