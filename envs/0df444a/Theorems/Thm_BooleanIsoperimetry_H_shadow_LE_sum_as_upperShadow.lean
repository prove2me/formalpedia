-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_shadow_LE_sum_as_upperShadow
-- name    : BooleanIsoperimetry.H_shadow_LE_sum_as_upperShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:48.246806+00:00
-- url     : https://prove2.me/theorems/bc8b78f2-7170-4922-9702-bee60605c965
-- title:
--   Boolean Isoperimetry: H shadow LE sum as upper Shadow
-- statement:
--   **Layer-sum bridge (sorry-free).**  Given the Macaulay layer decompositions of
--   `a, b, p, q` (each a full ball of radius `rx - 1` plus `tx` vertices of layer
--   `rx`, with `1 ≤ rx`), the LE/GT boundary sums are *exactly* the corresponding sums
--   of `binomPrefix` whole-layer terms plus `upperShadow` partial-layer terms.  This
--   makes precise that `H_shadow_LE_sum` / `H_shadow_GT_sum` are pure upper-shadow
--   (Kruskal–Katona/Macaulay) inequalities, and lets the leaves be checked
--   empirically by tabulating `upperShadow`.  It is a direct consequence of
--   `H_shadow_closed_form`, hence sorry-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L383-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L383-L394

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

theorem BooleanIsoperimetry.H_shadow_LE_sum_as_upperShadow {N a b p q ra rb rp rq ta tb tp tq : ℕ}
    (hra : 1 ≤ ra) (hrb : 1 ≤ rb) (hrp : 1 ≤ rp) (hrq : 1 ≤ rq)
    (hae : a = binomPrefix N ra + ta) (hbe : b = binomPrefix N rb + tb)
    (hpe : p = binomPrefix N rp + tp) (hqe : q = binomPrefix N rq + tq) :
    (H N p + H N q ≤ H N a + H N b) ↔
      (binomPrefix N (rp + 1) + upperShadow N rp tp)
        + (binomPrefix N (rq + 1) + upperShadow N rq tq)
      ≤ (binomPrefix N (ra + 1) + upperShadow N ra ta)
        + (binomPrefix N (rb + 1) + upperShadow N rb tb) := by sorry
