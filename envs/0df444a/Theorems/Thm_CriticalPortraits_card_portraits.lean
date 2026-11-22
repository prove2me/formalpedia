-- Prove2me | Theorems.Thm_CriticalPortraits_card_portraits
-- name    : CriticalPortraits.card_portraits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:32:07.300739+00:00
-- url     : https://prove2.me/theorems/804c6a58-22b6-4da8-b600-9ac8b5787685
-- title:
--   Critical Portraits: card portraits
-- statement:
--   **HEADLINE CENSUS THEOREM.** `#{portraits} = C(d*m, d-1) / d` for all `d` (and all `m`).
--
--   The number of degree-`d` portraits at level `m` equals `C(d·m, d−1) / d`. Follows from the
--   multiplicative form by `Nat.div_eq_of_eq_mul_right` (exact `ℕ`-division, no remainder).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L61-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean#L61-L64

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

theorem CriticalPortraits.card_portraits {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) / d := by sorry
