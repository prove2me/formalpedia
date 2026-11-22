-- Prove2me | Theorems.Thm_CriticalPortraits_betaParent_balance
-- name    : CriticalPortraits.betaParent_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:28.542173+00:00
-- url     : https://prove2.me/theorems/4b9afb0c-3d96-47c6-92d1-c036c3e7f9bb
-- title:
--   Critical Portraits: beta Parent balance
-- statement:
--   The balance identity at `betaK`: `Scount U (betaParent).val u.val = lu - betaK - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L443-L454
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L443-L454

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

theorem CriticalPortraits.betaParent_balance {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    (Scount U (betaParent U u).val u.val : ℤ)
      = ((u.val / m : ℕ) : ℤ) - ((betaK U u : ℕ) : ℤ) - 1 := by sorry
