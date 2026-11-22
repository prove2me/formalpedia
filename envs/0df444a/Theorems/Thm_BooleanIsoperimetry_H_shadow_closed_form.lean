-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_shadow_closed_form
-- name    : BooleanIsoperimetry.H_shadow_closed_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:48.530135+00:00
-- url     : https://prove2.me/theorems/9c6c0065-a0a0-4c77-b1dd-d612dfc6ec78
-- title:
--   Boolean Isoperimetry: H shadow closed form
-- statement:
--   **Macaulay closed form for `H` on a partial layer.**  For `1 ≤ r`, the
--   boundary of a full ball of radius `r-1` plus the first `t` vertices of layer `r`
--   equals the next full ball `binomPrefix N (r+1)` plus the upper shadow
--   `upperShadow N r t`.  This is sorry-free: it is just the definition of
--   `upperShadow` together with the monotonicity bound
--   `binomPrefix N (r+1) = H N (binomPrefix N r) ≤ H N (binomPrefix N r + t)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L76-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L76-L82

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.H_shadow_closed_form (N r t : ℕ) (hr : 1 ≤ r) :
    H N (binomPrefix N r + t) = binomPrefix N (r + 1) + upperShadow N r t := by sorry
