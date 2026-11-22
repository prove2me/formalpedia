-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_le_binomPrefix_of_layer
-- name    : BooleanIsoperimetry.H_le_binomPrefix_of_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:07.034045+00:00
-- url     : https://prove2.me/theorems/cbab0eef-5cbb-47af-bea2-ecd29a2e4c60
-- title:
--   Boolean Isoperimetry: H le binom Prefix of layer
-- statement:
--   **Two-layer confinement (LE regime).** If `b` lies at or below the top of
--   Macaulay layer `r` and `a ≤ H N b`, then `a` lies at or below the top of layer
--   `r+1`. Equivalently the LE-regime shadow comparison is confined to the two
--   adjacent Macaulay layers `r` and `r+1`. This is the reusable cascade-layer
--   increment fact behind the Case-I Kruskal–Katona/Macaulay window comparison.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L604-L609
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L604-L609

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

theorem BooleanIsoperimetry.H_le_binomPrefix_of_layer (N a b r : ℕ)
    (hb : b ≤ binomPrefix N (r + 1)) (hcase : a ≤ H N b) :
    a ≤ binomPrefix N (r + 2) := by sorry
