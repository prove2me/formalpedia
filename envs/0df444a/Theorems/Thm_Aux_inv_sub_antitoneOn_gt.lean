-- Prove2me | Theorems.Thm_Aux_inv_sub_antitoneOn_gt
-- name    : Aux.inv_sub_antitoneOn_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:51:01.332976+00:00
-- url     : https://prove2.me/theorems/0a52b97f-4a4f-4ee3-9e79-95c3bd8304df
-- title:
--   $x \mapsto (x-c)^{-1}$ is antitone on the open ray $(c, \infty)$
-- statement:
--   Let $R$ be a linearly ordered field (a field with a linear order making it a strict ordered ring) and let $c \in R$. Then the function
--   $$x \longmapsto \frac{1}{x - c}$$
--   is antitone (order-reversing) on the open ray $(c, \infty) = \{x \in R : x > c\}$: whenever $c < x \le y$, one has $(y-c)^{-1} \le (x-c)^{-1}$.
--
--   On this ray $x - c$ is positive and increasing in $x$, so its reciprocal is decreasing. This is the unbounded-interval companion of the corresponding statement on closed intervals $[a,b]$ with $c < a$.
--
--   It serves as a reusable monotonicity ingredient in integral-comparison arguments (e.g. bounding sums $\sum (n-c)^{-1}$ by integrals) within the sieve portion of the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L110-L116

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

theorem Aux.inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by sorry
