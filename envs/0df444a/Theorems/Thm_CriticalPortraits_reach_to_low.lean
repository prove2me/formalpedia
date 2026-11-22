-- Prove2me | Theorems.Thm_CriticalPortraits_reach_to_low
-- name    : CriticalPortraits.reach_to_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:08.225762+00:00
-- url     : https://prove2.me/theorems/e627c2f6-80e4-43cd-8e16-efef58ab8858
-- title:
--   Critical Portraits: reach to low
-- statement:
--   Every survivor `z` reaches the bottom survivor `q` of its block (predecessor a non-survivor).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L909-L923
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L909-L923

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.reach_to_low [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    ∀ n : ℕ, ∀ z : ZMod (d*m), z.val = n → (hz : z ∈ T P) →
      ∃ q, ∃ hq : q ∈ T P, predIn P q hq ∉ T P ∧
        hostSet P q hq = hostSet P z hz ∧ Relation.ReflTransGen (edgeStep P) z q := by sorry
