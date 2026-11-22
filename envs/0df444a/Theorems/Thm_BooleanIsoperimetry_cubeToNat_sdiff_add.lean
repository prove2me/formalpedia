-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_sdiff_add
-- name    : BooleanIsoperimetry.cubeToNat_sdiff_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:59.306466+00:00
-- url     : https://prove2.me/theorems/7df747eb-eb23-42fb-9c54-d320710b7051
-- title:
--   Boolean Isoperimetry: cube To Nat sdiff add
-- statement:
--   Binary value splits across a subset/complement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L644-L646
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L644-L646

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

theorem BooleanIsoperimetry.cubeToNat_sdiff_add {N} {U S : Cube N} (h : U ⊆ S) :
    cubeToNat (S \ U) + cubeToNat U = cubeToNat S := by sorry
