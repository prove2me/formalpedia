-- Prove2me | Theorems.Thm_Aux_log_le_sum_inv
-- name    : Aux.log_le_sum_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:51:25.799634+00:00
-- url     : https://prove2.me/theorems/ed836ca7-b4b0-4a84-89a4-ac1ad3b0e2cb
-- title:
--   $\log y$ is bounded by the harmonic sum up to $\lfloor y \rfloor$
-- statement:
--   Let $y \ge 1$ be a real number. Then the natural logarithm of $y$ is bounded above by the partial harmonic sum over the integers from $1$ to $\lfloor y \rfloor$:
--   $$\log y \;\le\; \sum_{d = 1}^{\lfloor y \rfloor} \frac{1}{d}.$$
--   Here $\lfloor y \rfloor$ denotes the (natural-number) floor of $y$.
--
--   This is the elementary integral-comparison bound $\log y = \int_1^y \frac{dt}{t} \le \sum_{d \le y} \frac{1}{d}$, obtained by comparing the integrand on each interval $[d, d+1]$ with the left endpoint value $1/d$.
--
--   In the PNT+ sieve development it provides the standard lower-bound input for sums of reciprocals over a sifting range, e.g. showing that the Selberg sieve main-term denominator $\sum_{d \le z} 1/d$ (and its multiplicative refinements) grows at least like $\log z$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L146-L154

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

theorem Aux.log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by sorry
