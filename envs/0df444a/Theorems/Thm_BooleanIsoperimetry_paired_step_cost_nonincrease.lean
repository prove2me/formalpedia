-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paired_step_cost_nonincrease
-- name    : BooleanIsoperimetry.paired_step_cost_nonincrease
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:42.783796+00:00
-- url     : https://prove2.me/theorems/307553a0-cb52-44ef-b402-fa6c9fdc7488
-- title:
--   Boolean Isoperimetry: paired step cost nonincrease
-- statement:
--   The Boolean Isoperimetry construction uses the paired step cost nonincrease property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L303-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L303-L310

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

theorem BooleanIsoperimetry.paired_step_cost_nonincrease {N : ℕ} {A B A' B' : Finset (Cube N)}
    (step : IsPairedCompressionStep A B A' B') :
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by sorry
