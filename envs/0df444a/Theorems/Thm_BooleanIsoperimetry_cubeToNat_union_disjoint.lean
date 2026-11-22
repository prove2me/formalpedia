-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_union_disjoint
-- name    : BooleanIsoperimetry.cubeToNat_union_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:59.638528+00:00
-- url     : https://prove2.me/theorems/563e4397-a70a-4d0b-a81d-757330e0d46f
-- title:
--   Boolean Isoperimetry: cube To Nat union disjoint
-- statement:
--   Binary value is additive over disjoint unions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L639-L641
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L639-L641

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

theorem BooleanIsoperimetry.cubeToNat_union_disjoint {N} {s t : Cube N} (h : Disjoint s t) :
    cubeToNat (s ∪ t) = cubeToNat s + cubeToNat t := by sorry
