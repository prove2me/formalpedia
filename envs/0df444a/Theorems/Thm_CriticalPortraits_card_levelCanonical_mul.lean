-- Prove2me | Theorems.Thm_CriticalPortraits_card_levelCanonical_mul
-- name    : CriticalPortraits.card_levelCanonical_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:18.586105+00:00
-- url     : https://prove2.me/theorems/33acb213-a87c-4654-aecf-2bb301263df9
-- title:
--   Critical Portraits: card level Canonical mul
-- statement:
--   **PRIMARY.** `d · #{canonical (d-1)-subsets} = C(d*m, d-1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Denominator.lean#L636-L651
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Denominator.lean#L636-L651

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
open _root_.CriticalPortraits.Cycle
variable {d m : ℕ}

theorem CriticalPortraits.card_levelCanonical_mul (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}
      = (d * m).choose (d - 1) := by sorry
