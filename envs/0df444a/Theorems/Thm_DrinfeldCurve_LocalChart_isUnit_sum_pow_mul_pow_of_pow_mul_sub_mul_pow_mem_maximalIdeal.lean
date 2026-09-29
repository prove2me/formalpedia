-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
-- name    : DrinfeldCurve.LocalChart.isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/9f2fbbde-28fa-52eb-8650-6ef414a7dd4e
-- title:
--   Dickson cofactor is a unit at 𝔽_q-rational directions
-- statement:
--   Let $q$ be a natural number assumed prime, and let $W$ be a commutative local ring whose maximal ideal $\mathfrak m_W$ contains the image of $q$, so that the residue field has characteristic $q$. Let $a,b\in W$ be such that at least one of $a$, $b$ lies outside $\mathfrak m_W$, and such that $a^q b - a b^q \in \mathfrak m_W$. The conclusion is that the element
--   $$\sum_{i=0}^{q} a^{(q-1)i}\, b^{(q-1)(q-i)}$$
--   of $W$ is a unit, the sum being over $i$ in the range $0,\dots,q$ and the exponents being formed with truncated natural subtraction (harmless here, since $q\ge 2$ and $i\le q$ throughout). In other words, for every pair $(a,b)$ whose reduction is a nonzero vector defining a point of $\mathbb P^1$ fixed by the relation $\bar a^q\bar b = \bar a\bar b^q$, the Dickson-type cofactor $H(a,b)=\sum_{i=0}^q a^{(q-1)i}b^{(q-1)(q-i)}$ is invertible in $W$.
--
--   The quantity $H(a,b)=\sum_{i=0}^{q}a^{(q-1)i}b^{(q-1)(q-i)}$ is the Dickson cofactor attached to the pair $(a,b)$, and the hypothesis $a^qb-ab^q\in\mathfrak m_W$ says exactly that the reduction of $(a:b)$ is a point of $\mathbb P^1(\mathbb F_q)$ inside $\mathbb P^1$ of the residue field. The statement supplies the invertibility clause used in the analysis of local charts, and is invoked in the study of homogeneous coefficients of the Drinfeld chart in [`FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W] (hqW : (q : W) ∈ maximalIdeal W)
    (a b : W) (hab : a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W)
    (hdir : a ^ q * b - a * b ^ q ∈ maximalIdeal W) :
    IsUnit (∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i))) := by sorry
