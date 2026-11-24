-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_bsm_iff_bddAbove_of_rate_zero
-- name    : BalanceSpecification.Growth.bsm_iff_bddAbove_of_rate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:31.900617+00:00
-- url     : https://prove2.me/theorems/e33dc7e6-79e4-4056-aa4a-7674be881f21
-- title:
--   Growth: bsm iff bdd Above of rate zero
-- statement:
--   At zero limiting growth, BSM is exactly boundedness of the counts. The
--   symbolic-dynamics consequence about periodic points requires its own proof.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L178-L197
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L178-L197

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

theorem BalanceSpecification.Growth.bsm_iff_bddAbove_of_rate_zero {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) (hz : rate a = 0) :
    BoundedSupermultiplicative a ↔ BddAbove (range a) := by sorry
