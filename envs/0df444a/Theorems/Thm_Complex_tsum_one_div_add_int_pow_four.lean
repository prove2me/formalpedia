-- Prove2me | Theorems.Thm_Complex_tsum_one_div_add_int_pow_four
-- name    : Complex.tsum_one_div_add_int_pow_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4a6ecf59-ab93-5aa7-890b-d0e993f42a13
-- title:
--   Fourth-order Lipschitz formula sum_{n∈ℤ}(x+n)⁻⁴
-- statement:
--   Let $x$ be a real number with the property that $x \neq n$ for every integer $n$, i.e. $x$ is not an integer. Then the sum over all integers $n$ of $1/(x+n)^4$, formed in $\mathbb{C}$ with $x$ regarded as a complex number and taken as an unconditional infinite sum indexed by $\mathbb{Z}$, equals
--   $$\frac{(2\pi i)^4}{6}\cdot\frac{q\,(q^2+4q+1)}{(1-q)^4},\qquad q = \exp(2\pi i x),$$
--   where $\pi$ is the real circle constant coerced to $\mathbb{C}$ and $i$ is the complex unit. The hypothesis that $x$ is not an integer guarantees both that no term $(x+n)^4$ on the left vanishes and that $1-q \neq 0$ on the right. Note that the identity is asserted for real arguments $x$ only, not for complex $x$ off the real line, and the left-hand side is a tsum over $\mathbb{Z}$, so the assertion includes in particular that this family is summable with the stated value.
--
--   This is the fourth-order instance of the Lipschitz (Hurwitz) partial-fraction expansion, obtained classically by differentiating the cotangent expansion $\sum_n (x+n)^{-2} = \pi^2/\sin^2(\pi x)$ twice. It is used to evaluate the constant terms of weight-four forms at torsion points, and is cited by the constructions of modular forms of weight four on the full level and on $\Gamma_H$ whose $q$-expansions match a prescribed combination of a square of a cusp-point term and the Eisenstein coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_tsum_one_div_add_int_pow_four.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
open Complex

theorem Complex.tsum_one_div_add_int_pow_four (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 4 =
      (2 * π * I) ^ 4 / 6 *
        (Complex.exp (2 * π * I * x) * (Complex.exp (2 * π * I * x) ^ 2 + 4 * Complex.exp (2 * π * I * x) + 1) /
          (1 - Complex.exp (2 * π * I * x)) ^ 4) := by sorry
