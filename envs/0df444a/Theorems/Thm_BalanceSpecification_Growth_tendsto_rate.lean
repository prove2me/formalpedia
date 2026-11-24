-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_tendsto_rate
-- name    : BalanceSpecification.Growth.tendsto_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:24.75883+00:00
-- url     : https://prove2.me/theorems/5a613df2-29ad-43dd-bf9e-a38c9532d453
-- title:
--   Growth: tendsto rate
-- statement:
--   The infimum formula denotes the actual limit, by Fekete's lemma.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L44-L48
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L44-L48

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth

theorem BalanceSpecification.Growth.tendsto_rate {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) :
    Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 (rate a)) := by sorry
