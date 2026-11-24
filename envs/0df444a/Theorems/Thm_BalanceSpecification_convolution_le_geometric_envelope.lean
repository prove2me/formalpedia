-- Prove2me | Theorems.Thm_BalanceSpecification_convolution_le_geometric_envelope
-- name    : BalanceSpecification.convolution_le_geometric_envelope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:05.605454+00:00
-- url     : https://prove2.me/theorems/326fdd96-990e-4fd8-9a48-f0bb5393a5fc
-- title:
--   Balance Specification: convolution le geometric envelope
-- statement:
--   Convolution of a sequence growing at most as `ρ^n` with a strictly slower
--   geometric family admits a uniform envelope at the base `ρ`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L109-L116
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L109-L116

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

theorem BalanceSpecification.convolution_le_geometric_envelope
    {a b : ℕ → ℝ} {θ ρ C : ℝ} (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ)
    (hC : 0 ≤ C) (hb0 : ∀ l : ℕ, 0 ≤ b l)
    (hb : ∀ l : ℕ, b l ≤ C * θ ^ l) (ha : ∀ n : ℕ, a n ≤ ρ ^ n) (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l * a (n - l)) ≤
      (C / (1 - θ / ρ)) * ρ ^ n := by sorry
