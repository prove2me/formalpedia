-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_ratio_tendsto_zero_of_exp_gap
-- name    : BalanceSpecification.Growth.ratio_tendsto_zero_of_exp_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:52.867827+00:00
-- url     : https://prove2.me/theorems/8afc85ad-8762-4c39-9856-56b914b0cd1c
-- title:
--   Growth: ratio tendsto zero of exp gap
-- statement:
--   An eventual upper exponential with strictly smaller exponent than a lower
--   exponential makes the quotient tend to zero. Zero numerators are permitted.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L129-L152
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L129-L152

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
open BalanceSpecification.Growth

theorem BalanceSpecification.Growth.ratio_tendsto_zero_of_exp_gap {a b : ℕ → ℝ} {α β : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hgap : α < β)
    (hupper : ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp ((n : ℝ) * α))
    (hlower : ∀ n : ℕ, Real.exp ((n : ℝ) * β) ≤ b n) :
    Tendsto (fun n => a n / b n) atTop (𝓝 0) := by sorry
