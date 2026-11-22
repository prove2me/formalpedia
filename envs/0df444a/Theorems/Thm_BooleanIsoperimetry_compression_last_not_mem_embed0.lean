-- Prove2me | Theorems.Thm_BooleanIsoperimetry_compression_last_not_mem_embed0
-- name    : BooleanIsoperimetry.compression_last_not_mem_embed0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:41.25723+00:00
-- url     : https://prove2.me/theorems/8a0e5e6b-ab50-4512-bbdf-d716435cd7a2
-- title:
--   Boolean Isoperimetry: compression last not mem embed0
-- statement:
--   The top coordinate never lies in an `embed0` image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L51-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L51-L53

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

theorem BooleanIsoperimetry.compression_last_not_mem_embed0 {N : ℕ} (x : Cube N) :
    Fin.last N ∉ embed0 x := by sorry
