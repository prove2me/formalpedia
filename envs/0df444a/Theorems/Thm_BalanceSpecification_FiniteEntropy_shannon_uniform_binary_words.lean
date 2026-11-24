-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_uniform_binary_words
-- name    : BalanceSpecification.FiniteEntropy.shannon_uniform_binary_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:14.135312+00:00
-- url     : https://prove2.me/theorems/408977f6-8547-40c7-9070-c4b4c58842bf
-- title:
--   Finite Entropy: shannon uniform binary words
-- statement:
--   On binary words of length `n`, the fair distribution contributes `n log 2`.
--   This makes the source's distinction between all words and length-`n` words explicit.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L79-L84
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L79-L84

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]

theorem BalanceSpecification.FiniteEntropy.shannon_uniform_binary_words (n : ℕ) :
    shannon (fun _ : Fin n → Bool =>
      1 / (Fintype.card (Fin n → Bool) : ℝ)) = (n : ℝ) * Real.log 2 := by sorry
