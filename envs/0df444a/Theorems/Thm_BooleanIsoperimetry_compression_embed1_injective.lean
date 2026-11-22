-- Prove2me | Theorems.Thm_BooleanIsoperimetry_compression_embed1_injective
-- name    : BooleanIsoperimetry.compression_embed1_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:34.878474+00:00
-- url     : https://prove2.me/theorems/be49f726-30bc-420b-b3da-1db70c126ad5
-- title:
--   Boolean Isoperimetry: compression embed1 injective
-- statement:
--   `embed1` is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L56-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L56-L62

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

theorem BooleanIsoperimetry.compression_embed1_injective {N : ℕ} : Function.Injective (@embed1 N) := by sorry
