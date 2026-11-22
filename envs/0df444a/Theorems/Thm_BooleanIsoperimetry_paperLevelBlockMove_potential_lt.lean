-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_potential_lt
-- name    : BooleanIsoperimetry.paperLevelBlockMove_potential_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:08.501041+00:00
-- url     : https://prove2.me/theorems/ebc16409-6c51-4838-a4cc-897902d30181
-- title:
--   Boolean Isoperimetry: paper Level Block Move potential lt
-- statement:
--   The Boolean Isoperimetry construction uses the paper Level Block Move potential lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1271-L1277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1271-L1277

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

theorem BooleanIsoperimetry.paperLevelBlockMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : compressionPotential A' < compressionPotential A := by sorry
