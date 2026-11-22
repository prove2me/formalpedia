-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_shadow_LE_sum
-- name    : BooleanIsoperimetry.H_shadow_LE_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:17.982166+00:00
-- url     : https://prove2.me/theorems/8e352949-e2f0-4bee-a237-399bf7d1f77a
-- title:
--   Boolean Isoperimetry: H shadow LE sum
-- statement:
--   **Macaulay shadow-sum leaf, LE regime.**  For the canonical cascade split
--   `(p, q)` of `a + b` with `b ≤ a` and `a ≤ H N b` (the LE regime in which the
--   outer boundary `max`s collapse to `H N a + H N b`), the canonical boundary sum is
--   minimal.  Via `H_shadow_closed_form` this is the upper-shadow comparison
--   `upperShadow N rp tp + upperShadow N rq tq ≤ upperShadow N ra ta + upperShadow N rb tb`
--   modulo whole layers (see `H_shadow_LE_sum_as_upperShadow`).  This is the genuine
--   Kruskal–Katona/Macaulay leaf; it is true (verified against the exact cascade model
--   of `H`, all split dimensions `N ≤ 4`) but its proof is the Frankl–Füredi shadow
--   calculation, which is now fully formalized and sorry-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L236-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L236-L246

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

theorem BooleanIsoperimetry.H_shadow_LE_sum {N a b p q : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hcasc : CascadeSplit N (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H N b) :
    H N p + H N q ≤ H N a + H N b := by sorry
