-- Prove2me | Theorems.Thm_BooleanIsoperimetry_PairShadowCost_initSeg_eq_max_H
-- name    : BooleanIsoperimetry.PairShadowCost_initSeg_eq_max_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:41.342055+00:00
-- url     : https://prove2.me/theorems/bba830d2-7708-4606-863f-a470677bcc65
-- title:
--   Boolean Isoperimetry: Pair Shadow Cost init Seg eq max H
-- statement:
--   On canonical initial segments the paired slice functional is exactly the
--   scalar max expression used in the cascade recurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L176-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L176-L180

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.PairShadowCost_initSeg_eq_max_H {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) =
      max (H N a) b + max (H N b) a := by sorry
