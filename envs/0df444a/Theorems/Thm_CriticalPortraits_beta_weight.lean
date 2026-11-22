-- Prove2me | Theorems.Thm_CriticalPortraits_beta_weight
-- name    : CriticalPortraits.beta_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:15.803536+00:00
-- url     : https://prove2.me/theorems/d2dd4615-fb26-45d2-96d9-83197fcb3889
-- title:
--   Critical Portraits: beta weight
-- statement:
--   **Weight.** `∑ S ∈ β U, (|S| - 1) = d - 1` (counted via `T(β U) = U`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L877-L895
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L877-L895

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

theorem CriticalPortraits.beta_weight {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcard : U.card = d - 1) (hcanon : LevelCanonical d m U) :
    ∑ S ∈ beta U, (S.card - 1) = d - 1 := by sorry
