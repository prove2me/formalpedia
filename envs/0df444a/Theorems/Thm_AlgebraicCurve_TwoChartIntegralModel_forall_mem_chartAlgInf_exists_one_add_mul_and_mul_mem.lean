-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem
-- name    : AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/8f2488b5-6f47-5e7f-a477-1719b351ada8
-- title:
--   Pole chart of j' lies in a unipotent localisation of A_∞(j)
-- statement:
--   Let $R$ be a commutative ring and $F$ a field equipped with an $R$-algebra structure, and let $j, j' \in F$ be non-zero. For a subset $S \subseteq F$ the chart algebra `chartAlg R F S` is the subalgebra of $F$ consisting of all elements integral over the $R$-subalgebra $R[S] =$ `Algebra.adjoin R S`, i.e. the integral closure of $R[S]$ in $F$; `chartAlgInf R F j` is the case $S = \{j^{-1}\}$. Assume the localised integrality hypothesis `hloc`: there exist $b \in R[j^{-1}]$ and $c \in F$ such that $c\,(1 + j^{-1} b) = 1$ and $j'^{-1}$ is integral over $R[j^{-1}, c]$. The conclusion is that for every $y \in$ `chartAlgInf R F j'`, that is every $y \in F$ integral over $R[j'^{-1}]$, there exists $s \in$ `chartAlgInf R F j` such that, first, $s = 1 + j^{-1} a$ for some $a \in$ `chartAlgInf R F j`, and second, $s\,y \in$ `chartAlgInf R F j`. Thus every element of the pole chart of $j'$ becomes integral over $R[j^{-1}]$ after multiplication by a single element of the pole chart of $j$ congruent to $1$ modulo $j^{-1}$.
--
--   This is the denominator-bounding step that lets the pole chart of one parameter be seen inside a localisation of the pole chart of another at an element congruent to $1$ modulo $j^{-1}$; it supplies the second hypothesis of the two-chart gluing statement for integral models of modular curves. It is used in the integrality comparison for $q$-expansions and in the variant phrased with an integrality hypothesis on a product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hloc : ∃ b ∈ Algebra.adjoin R ({j⁻¹} : Set F), ∃ c : F,
      c * (1 + j⁻¹ * b) = 1 ∧ IsIntegral (Algebra.adjoin R ({j⁻¹, c} : Set F)) j'⁻¹) :
    ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j := by sorry
