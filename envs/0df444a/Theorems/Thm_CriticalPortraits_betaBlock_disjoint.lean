-- Prove2me | Theorems.Thm_CriticalPortraits_betaBlock_disjoint
-- name    : CriticalPortraits.betaBlock_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:03.982642+00:00
-- url     : https://prove2.me/theorems/3e3adf5b-f332-4302-bcd4-71ceac991479
-- title:
--   Critical Portraits: beta Block disjoint
-- statement:
--   Distinct blocks are vertex-disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L853-L862
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L853-L862

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.betaBlock_disjoint {d m : ℕ} {U : Finset (ZMod (d * m))} {v1 v2 : ZMod (d * m)}
    (hne : betaBlock U v1 ≠ betaBlock U v2) : Disjoint (betaBlock U v1) (betaBlock U v2) := by sorry
