-- Prove2me | Theorems.Thm_Aux_sum_pow_cardDistinctFactors_le_self_mul_log_pow
-- name    : Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:52:17.344639+00:00
-- url     : https://prove2.me/theorems/9119b45a-dbe0-40ee-98ba-88ed5423e26b
-- title:
--   Divisor sum of $h^{\omega(d)}$ up to $x$ is at most $x(1+\log x)^h$
-- statement:
--   Let $P$ be a squarefree natural number, let $h$ be a natural number, and let $x \ge 1$ be real. Then the sum of the $h$-th power of the number-of-distinct-prime-factors function over divisors of $P$ up to $x$ satisfies
--   $$\sum_{\substack{d \mid P \\ d \le x}} h^{\omega(d)} \;\le\; x \,(1 + \log x)^h,$$
--   where $\omega(d)$ denotes the number of distinct prime factors of $d$ (formally the sum is over $d \in \mathrm{divisors}(P)$ with the indicator $[d \le x]$, and $h^{\omega(d)}$ is taken in $\mathbb{R}$).
--
--   The proof idea behind such bounds is that $h^{\omega(d)}$ counts factorizations of $d$ into $h$ ordered coprime parts, so the sum is at most $\big(\sum_{m \le x} 1\big)$-type quantities controlled by $x$ times the $h$-th power of the harmonic-sum bound $\sum_{m \le x} 1/m \le 1 + \log x$.
--
--   This estimate controls the error-term contribution in the Selberg sieve (and in Brun–Titchmarsh-type applications), where remainders are weighted by $3^{\omega(d)}$-type divisor factors; it converts these into the polylogarithmic loss $(1+\log z)^h$ seen in the final sieve bounds.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L253-L269

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

open ArithmeticFunction.IsMultiplicative

variable {R : Type*}

open Aux

theorem Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by sorry
