-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_log_div_bddBelow
-- name    : BalanceSpecification.Growth.log_div_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:46.558195+00:00
-- url     : https://prove2.me/theorems/8d88bcff-f4f9-4a29-bb7f-59aa6298af32
-- title:
--   Growth: log div bdd Below
-- statement:
--   The Growth construction uses the log div bdd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L37-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L37-L41

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

theorem BalanceSpecification.Growth.log_div_bddBelow {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) :
    BddBelow (range fun n : ℕ => Real.log (a n) / n) := by sorry
