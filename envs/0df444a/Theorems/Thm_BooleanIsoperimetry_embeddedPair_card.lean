-- Prove2me | Theorems.Thm_BooleanIsoperimetry_embeddedPair_card
-- name    : BooleanIsoperimetry.embeddedPair_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:40.54796+00:00
-- url     : https://prove2.me/theorems/74fd45e9-54d5-4247-8568-2996ce074f9b
-- title:
--   Boolean Isoperimetry: embedded Pair card
-- statement:
--   The Boolean Isoperimetry construction uses the embedded Pair card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L113-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L113-L118

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

theorem BooleanIsoperimetry.embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    (embeddedPair N A B).card = A.card + B.card := by sorry
