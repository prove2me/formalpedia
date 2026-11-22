-- Prove2me | Theorems.Thm_CriticalPortraits_noEscape
-- name    : CriticalPortraits.noEscape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:25.020031+00:00
-- url     : https://prove2.me/theorems/ce876ff0-297e-4d13-b381-2cdc8d729dee
-- title:
--   Critical Portraits: no Escape
-- statement:
--   **P (no escape).** For an edge `(v,u) = (v*(u), u)` of canonical `U` and an interior survivor
--       `s` (`v < s.val < u.val`), the balance parent of `s` does not escape below `v`:
--       `v*(u).val ≤ v*(s).val`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1197-L1280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1197-L1280

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

theorem CriticalPortraits.noEscape {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u s : ZMod (d * m)} (hu : u ∈ U) (hs : s ∈ U)
    (hslo : (betaParent U u).val < s.val) (hshi : s.val < u.val) :
    (betaParent U u).val ≤ (betaParent U s).val := by sorry
