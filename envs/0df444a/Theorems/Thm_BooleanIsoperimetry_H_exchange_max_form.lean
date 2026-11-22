-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_exchange_max_form
-- name    : BooleanIsoperimetry.H_exchange_max_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:58.61822+00:00
-- url     : https://prove2.me/theorems/38e7321b-27d8-4503-9e9d-e7a8241cb227
-- title:
--   Boolean Isoperimetry: H exchange max form
-- statement:
--   Regime-free max-form exchange theorem, assembled from the proved degenerate
--   `q = 0` branch and the positive Frankl–Füredi/Macaulay leaf.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L276-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L276-L300

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

theorem BooleanIsoperimetry.H_exchange_max_form {N s p q a b : ℕ}
    (hpq : CascadeSplit N s p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hab : a + b = s) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by sorry
