-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_ratio_tendsto_zero_of_rate_gap
-- name    : BalanceSpecification.Growth.ratio_tendsto_zero_of_rate_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:08.725675+00:00
-- url     : https://prove2.me/theorems/fa745cb7-d9b3-41e2-8040-d3ae008de1df
-- title:
--   Growth: ratio tendsto zero of rate gap
-- statement:
--   Positive submultiplicative numerator counts with limiting growth below the
--   denominator's exponential lower bound have vanishing quotient. The premise
--   `1 ≤ a n` is explicit and must not be applied to an empty avoidance language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L157-L172
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L157-L172

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

theorem BalanceSpecification.Growth.ratio_tendsto_zero_of_rate_gap {a b : ℕ → ℝ} {β : ℝ}
    (ha : ∀ n, 1 ≤ a n) (hsa : Submultiplicative a)
    (hgap : rate a < β) (hlower : ∀ n : ℕ, Real.exp ((n : ℝ) * β) ≤ b n) :
    Tendsto (fun n => a n / b n) atTop (𝓝 0) := by sorry
