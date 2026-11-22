-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_neighborhood_card_le
-- name    : BooleanIsoperimetry.paperColexBlockMove_neighborhood_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:07.257376+00:00
-- url     : https://prove2.me/theorems/a3afd242-2984-4ee5-9646-aaabfe013230
-- title:
--   Boolean Isoperimetry: paper Colex Block Move neighborhood card le
-- statement:
--   The Boolean Isoperimetry construction uses the paper Colex Block Move neighborhood card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1172-L1201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1172-L1201

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

theorem BooleanIsoperimetry.paperColexBlockMove_neighborhood_card_le {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by sorry
