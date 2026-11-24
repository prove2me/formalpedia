-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_rate_mono
-- name    : BalanceSpecification.Growth.rate_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:51.270029+00:00
-- url     : https://prove2.me/theorems/4d40261c-31ec-4c83-b26d-fca10dc90513
-- title:
--   Growth: rate mono
-- statement:
--   Pointwise domination of count sequences implies domination of their
--   limiting entropies.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L169-L174
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L169-L174

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

theorem BalanceSpecification.Growth.rate_mono {a b : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) (hb : ∀ n, 1 ≤ b n)
    (hsa : Submultiplicative a) (hsb : Submultiplicative b)
    (hab : ∀ n, a n ≤ b n) : rate a ≤ rate b := by sorry
