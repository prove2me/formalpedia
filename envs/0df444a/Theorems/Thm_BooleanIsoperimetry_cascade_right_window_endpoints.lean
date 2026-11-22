-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_right_window_endpoints
-- name    : BooleanIsoperimetry.cascade_right_window_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:41.895831+00:00
-- url     : https://prove2.me/theorems/1d1bbcd5-8608-4b97-abda-a32092a66b67
-- title:
--   Boolean Isoperimetry: cascade right window endpoints
-- statement:
--   Endpoint arithmetic for the right-oriented equal-length Macaulay windows.  If
--   `a ≤ p`, then `q ≤ b`, and the two shadow windows `[a,p)` and `[q,b)` have the
--   same length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L342-L346
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L342-L346

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.cascade_right_window_endpoints {N a b p q : ℕ}
    (hcasc : CascadeSplit N (a + b) p q) (hap : a ≤ p) :
    q ≤ b ∧ p - a = b - q := by sorry
