-- Prove2me | Theorems.Thm_CriticalPortraits_betaRoot_of_mem
-- name    : CriticalPortraits.betaRoot_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:53.358858+00:00
-- url     : https://prove2.me/theorems/58e884a4-729d-46b9-97ab-4ad832bdb693
-- title:
--   Critical Portraits: beta Root of mem
-- statement:
--   If `x ∈ U`, the root descends to its parent's root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L562-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L562-L565

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

theorem CriticalPortraits.betaRoot_of_mem {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    betaRoot hd hm hcanon x = betaRoot hd hm hcanon (betaParent U x) := by sorry
