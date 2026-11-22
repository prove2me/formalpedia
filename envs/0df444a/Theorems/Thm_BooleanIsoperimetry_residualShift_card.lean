-- Prove2me | Theorems.Thm_BooleanIsoperimetry_residualShift_card
-- name    : BooleanIsoperimetry.residualShift_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:57.983819+00:00
-- url     : https://prove2.me/theorems/e0569302-b9e6-4e39-8f1b-55f2789827c7
-- title:
--   Boolean Isoperimetry: residual Shift card
-- statement:
--   The Boolean Isoperimetry construction uses the residual Shift card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L563-L564
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L563-L564

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

theorem BooleanIsoperimetry.residualShift_card {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsDownFixedResidualShift A A') : A'.card = A.card := by sorry
