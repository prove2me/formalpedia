-- Prove2me | Theorems.Thm_Erdos685_primeFactors_card_le_cutoff
-- name    : Erdos685.primeFactors_card_le_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:41:37.809068+00:00
-- url     : https://prove2.me/theorems/9605daad-36e9-4a70-b339-39ae8eb5e9da
-- title:
--   Erdos685: prime Factors card le cutoff
-- statement:
--   A cutoff bounds the number of distinct prime factors by counting the
--   small primes and charging every large prime at least `log T`.
--
--   Source: https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/PrimeCutoff.lean#L21-L74
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/PrimeCutoff.lean#L21-L74

module
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Asymptotic_PrimeCutoff
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open Erdos685

theorem Erdos685.primeFactors_card_le_cutoff {B : ℕ} (hB : 0 < B)
    {T : ℝ} (hT : 1 < T) :
    (B.primeFactors.card : ℝ) ≤ T + 1 + Real.log B / Real.log T := by sorry
