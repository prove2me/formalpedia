-- Prove2me | Theorems.Thm_BalanceSpecification_renewal_le_pow_of_pressure_le_one
-- name    : BalanceSpecification.renewal_le_pow_of_pressure_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:42.694473+00:00
-- url     : https://prove2.me/theorems/aec9f294-d339-4449-b49e-293454cfa77f
-- title:
--   Balance Specification: renewal le pow of pressure le one
-- statement:
--   A renewal recurrence has growth at most `ρ` when every finite portion of
--   its weighted code pressure is at most one. Nonnegativity of the coefficients
--   suffices; the estimated sequence itself may be arbitrary real-valued.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L21-L62
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L21-L62

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

theorem BalanceSpecification.renewal_le_pow_of_pressure_le_one
    {a g : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hg : ∀ n : ℕ, 0 ≤ g n)
    (ha0 : a 0 ≤ 1)
    (hrec : ∀ n : ℕ, a (n + 1) ≤
      ∑ l ∈ Finset.range (n + 1), g (l + 1) * a (n - l))
    (hpressure : ∀ n : ℕ,
      (∑ l ∈ Finset.range (n + 1), g (l + 1) / ρ ^ (l + 1)) ≤ 1)
    (n : ℕ) : a n ≤ ρ ^ n := by sorry
