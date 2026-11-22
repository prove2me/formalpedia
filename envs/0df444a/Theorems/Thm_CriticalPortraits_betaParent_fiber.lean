-- Prove2me | Theorems.Thm_CriticalPortraits_betaParent_fiber
-- name    : CriticalPortraits.betaParent_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:21.788535+00:00
-- url     : https://prove2.me/theorems/0abe300c-5597-4a99-8070-436197d99982
-- title:
--   Critical Portraits: beta Parent fiber
-- statement:
--   `betaParent` shares `u`'s fiber.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L279-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L279-L284

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

theorem CriticalPortraits.betaParent_fiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val % m = u.val % m := by sorry
