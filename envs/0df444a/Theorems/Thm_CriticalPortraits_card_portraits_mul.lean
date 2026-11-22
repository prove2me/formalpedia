-- Prove2me | Theorems.Thm_CriticalPortraits_card_portraits_mul
-- name    : CriticalPortraits.card_portraits_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:46.205555+00:00
-- url     : https://prove2.me/theorems/17f241cc-b03b-49c0-85cc-e34443f1bc6e
-- title:
--   Critical Portraits: card portraits mul
-- statement:
--   **PRIMARY (multiplicative form).** `d · #{portraits} = C(d*m, d-1)`.
--
--   The cleanest statement: the count of portraits times `d` equals the binomial numerator.
--   Proved by the `T`-bijection onto level-canonical `(d−1)`-subsets composed with
--   `card_levelCanonical_mul`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L42-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L42-L55

module
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Census
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset

theorem CriticalPortraits.card_portraits_mul {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) := by sorry
