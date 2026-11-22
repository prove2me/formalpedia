-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_exchange_max_form_pos
-- name    : BooleanIsoperimetry.H_exchange_max_form_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:18.568797+00:00
-- url     : https://prove2.me/theorems/88a45bd5-ea2f-44f4-90f8-17eea2d45b5b
-- title:
--   Boolean Isoperimetry: H exchange max form pos
-- statement:
--   **Positive Frankl–Füredi / Macaulay exchange step.**  For a positive
--   canonical cascade split `(p, q)` of `a + b` at level `N`, the canonical
--   cross-boundary cost is at most the cross-boundary cost of the arbitrary split
--   `(a, b)`.
--
--   This is the remaining PDF-layer theorem: the paired Up/Down compression plus the
--   Macaulay/Kruskal–Katona shadow comparison in the nondegenerate branch.  The
--   `q = 0` branch is proved separately below by direct cascade arithmetic, and the
--   full exchange theorem is assembled from the two branches.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L139-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L139-L154

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

theorem BooleanIsoperimetry.H_exchange_max_form_pos {N p q a b : ℕ}
    (hpq : CascadeSplit N (a + b) p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (_hq_pos : 1 ≤ q) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by sorry
