-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initialSlicePair_harper_bound
-- name    : BooleanIsoperimetry.initialSlicePair_harper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:33.841035+00:00
-- url     : https://prove2.me/theorems/b41312b0-5225-48bb-8077-c7ec06ec414b
-- title:
--   Boolean Isoperimetry: initial Slice Pair harper bound
-- statement:
--   **Embedded-pair Harper/Macaulay shadow comparison.**  Among families in
--   `Q_{N+1}` with `a+b` vertices, the simplicial initial segment has closed
--   neighborhood no larger than the particular two-slice family consisting of
--   canonical initial segments of sizes `a` and `b`.  Sorry-free corollary of
--   `harper_macaulay_min` via the cardinality bridge
--   `neighborhood_initialSlicePair_card`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L184-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L184-L189

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.initialSlicePair_harper_bound {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (simplicialInitSeg (N + 1) (a + b))).card ≤
      (neighborhood 1 (initialSlicePair N a b)).card := by sorry
