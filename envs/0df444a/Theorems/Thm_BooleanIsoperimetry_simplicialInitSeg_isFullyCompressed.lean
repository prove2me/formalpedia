-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_isFullyCompressed
-- name    : BooleanIsoperimetry.simplicialInitSeg_isFullyCompressed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:33.091194+00:00
-- url     : https://prove2.me/theorems/ac500892-f6db-4cd0-ad9c-89a38b7831df
-- title:
--   Boolean Isoperimetry: simplicial Init Seg is Fully Compressed
-- statement:
--   The simplicial initial segment is fully compressed (lower-level saturated and
--   colex-shift fixed): it is a rank-downward-closed set, so no colex shift or level
--   fill can apply.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2107-L2122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2107-L2122

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

theorem BooleanIsoperimetry.simplicialInitSeg_isFullyCompressed {N m : ℕ} :
    IsFullyCompressed (simplicialInitSeg N m) := by sorry
