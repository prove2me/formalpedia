-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_subset_familyUp
-- name    : BooleanIsoperimetry.familyUp_subset_familyUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:02.386839+00:00
-- url     : https://prove2.me/theorems/819db309-e704-42a0-b0b6-ec8f5e252bf3
-- title:
--   Boolean Isoperimetry: family Up subset family Up
-- statement:
--   The Boolean Isoperimetry construction uses the family Up subset family Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1069-L1082
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1069-L1082

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

theorem BooleanIsoperimetry.familyUp_subset_familyUp {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    {A B : Finset (Cube N)} (hsub : A ⊆ B) :
    familyUp U V A ⊆ familyUp U V B := by sorry
