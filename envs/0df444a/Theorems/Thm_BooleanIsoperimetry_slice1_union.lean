-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_union
-- name    : BooleanIsoperimetry.slice1_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:42.677186+00:00
-- url     : https://prove2.me/theorems/300652c8-835e-4e57-b12a-c5c386cad482
-- title:
--   Boolean Isoperimetry: slice1 union
-- statement:
--   The Boolean Isoperimetry construction uses the slice1 union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2417-L2420
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2417-L2420

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

theorem BooleanIsoperimetry.slice1_union {N : ℕ} (A B : Finset (Cube (N + 1))) :
    slice1 (A ∪ B) = slice1 A ∪ slice1 B := by sorry
