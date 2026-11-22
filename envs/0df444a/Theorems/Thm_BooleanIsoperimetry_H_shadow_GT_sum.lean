-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_shadow_GT_sum
-- name    : BooleanIsoperimetry.H_shadow_GT_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:22.737942+00:00
-- url     : https://prove2.me/theorems/5c6e804e-fc15-4a6c-a101-35a32483ac03
-- title:
--   Boolean Isoperimetry: H shadow GT sum
-- statement:
--   **Macaulay shadow-sum leaf, GT regime.**  For the canonical cascade split
--   `(p, q)` of `a + b` with `b ≤ a` and `H N b < a` (the GT/slack regime in which the
--   outer boundary `max (H N b) a` collapses to `a`), the canonical boundary sum is
--   bounded by `H N a + a`.  As with the LE leaf, via `H_shadow_closed_form` this is a
--   sum comparison of `upperShadow` quantities with the GT slack `a`.  This is the
--   genuine GT shadow-deficit leaf of Frankl–Füredi; true (cascade-model verified) but
--   now fully formalized and sorry-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L255-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L255-L265

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

theorem BooleanIsoperimetry.H_shadow_GT_sum {N a b p q : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hcasc : CascadeSplit N (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H N b < a) :
    H N p + H N q ≤ H N a + a := by sorry
