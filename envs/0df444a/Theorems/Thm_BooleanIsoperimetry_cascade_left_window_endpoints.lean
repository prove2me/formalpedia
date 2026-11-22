-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_left_window_endpoints
-- name    : BooleanIsoperimetry.cascade_left_window_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:11.900802+00:00
-- url     : https://prove2.me/theorems/e5273554-cebc-4a23-967e-a91a66437f9f
-- title:
--   Boolean Isoperimetry: cascade left window endpoints
-- statement:
--   Endpoint arithmetic for the left-oriented equal-length Macaulay windows.  If
--   the canonical split `(p,q)` and the arbitrary split `(a,b)` have the same total
--   and `p ≤ a`, then the lower endpoint also moves inward, `b ≤ q`, and the two
--   shadow windows `[b,q)` and `[p,a)` have the same length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L331-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L331-L335

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

theorem BooleanIsoperimetry.cascade_left_window_endpoints {N a b p q : ℕ}
    (hcasc : CascadeSplit N (a + b) p q) (hpa : p ≤ a) :
    b ≤ q ∧ a - p = q - b := by sorry
