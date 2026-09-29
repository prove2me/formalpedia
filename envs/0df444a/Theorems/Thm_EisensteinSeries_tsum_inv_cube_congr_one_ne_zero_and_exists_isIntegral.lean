-- Prove2me | Theorems.Thm_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
-- name    : EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/68fa1a03-bc4d-529a-904b-f3f17f8bfba7
-- title:
--   Non-vanishing and N-unit integrality of sum_{d≡ 1 (N)} d⁻³
-- statement:
--   Let $N$ be a natural number with $3 \le N$, and let $S = \sum' ((d:\mathbb{C})^3)^{-1}$ denote the unordered sum (Mathlib's `tsum`) over the subtype of integers $d$ whose image in $\mathbb{Z}/N\mathbb{Z}$ equals $1$. The theorem asserts a conjunction. First, $S \neq 0$. Second, writing $x = \dfrac{2}{(2\pi i)^3}\, S$, where $\pi$ is the real number $\pi$ coerced into $\mathbb{C}$ and $i$ is the complex imaginary unit, there exists a natural number $a$ such that both $N^a x$ and $N^a x^{-1}$ are integral over $\mathbb{Z}$, that is, each is a root of a monic polynomial with integer coefficients. The exponent $a$ is quantified once and serves both integrality assertions, so that $x$ is a nonzero element of $\overline{\mathbb{Q}}$ which becomes a unit after inverting $N$ in the algebraic integers. The inverse is the field inverse in $\mathbb{C}$; the first conjunct guarantees that it is not formed by Lean's convention $0^{-1} = 0$.
--
--   The quantity $x$ is the constant term at the cusp $\infty$ of the weight-three Eisenstein series of level $N$ attached to the pair $(0,1)$ modulo $N$, the series $S$ being a partial zeta value at $s = 3$ that is classically evaluated through the periodic Bernoulli function; here that evaluation is supplied by [`ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun`](thm.html#ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun). It is used by [`ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion`](thm.html#ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion), where dividing by this constant term must be possible without losing integrality of the $q$-expansion away from $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
    (N : ℕ) (hN : 3 ≤ N) :
    (∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹) ≠ 0 ∧
    ∃ a : ℕ,
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)) ∧
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)⁻¹) := by sorry
