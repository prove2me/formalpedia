-- Prove2me | Theorems.Thm_BalanceSpecification_convolution_le_pow_of_weighted_sum_bound
-- name    : BalanceSpecification.convolution_le_pow_of_weighted_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:43.734209+00:00
-- url     : https://prove2.me/theorems/66401763-9b30-43bb-a509-17e3be09f758
-- title:
--   Balance Specification: convolution le pow of weighted sum bound
-- statement:
--   A family with a uniformly bounded weighted finite sum can be convolved
--   with a renewal sequence without changing its exponential base.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L66-L85
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L66-L85

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.convolution_le_pow_of_weighted_sum_bound
    {a b : ℕ → ℝ} {ρ B : ℝ} (hρ : 0 < ρ) (hb : ∀ n : ℕ, 0 ≤ b n)
    (ha : ∀ n : ℕ, a n ≤ ρ ^ n)
    (hsum : ∀ n : ℕ, (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) ≤ B)
    (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l * a (n - l)) ≤ B * ρ ^ n := by sorry
