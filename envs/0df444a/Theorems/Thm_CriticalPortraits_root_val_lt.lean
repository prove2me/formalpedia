-- Prove2me | Theorems.Thm_CriticalPortraits_root_val_lt
-- name    : CriticalPortraits.root_val_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:47.734842+00:00
-- url     : https://prove2.me/theorems/ed76bcea-c2b8-4c9c-b140-23dd7424bc4a
-- title:
--   Critical Portraits: root val lt
-- statement:
--   A strict root `g` of `x`'s window (so `loV P x ≤ loV P g`, `hiV g ≤ hiV x`,
--       `colV g ≠ colV x`) has `g.val < x.val`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L669-L684
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L669-L684

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

theorem CriticalPortraits.root_val_lt [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {g x : ZMod (d * m)} (hg : g ∈ T P) (hx : x ∈ T P)
    (hlo : loV P x ≤ loV P g) (hhi : hiV g ≤ hiV x) (hcol : colV g ≠ colV x) : g.val < x.val := by sorry
