-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_potential_lt
-- name    : BooleanIsoperimetry.paperColexBlockMove_potential_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:50.699593+00:00
-- url     : https://prove2.me/theorems/28fe628e-2185-499e-929a-6406ceb391a8
-- title:
--   Boolean Isoperimetry: paper Colex Block Move potential lt
-- statement:
--   The Boolean Isoperimetry construction uses the paper Colex Block Move potential lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1203-L1220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1203-L1220

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

theorem BooleanIsoperimetry.paperColexBlockMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : compressionPotential A' < compressionPotential A := by sorry
