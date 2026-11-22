-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperColexShiftMove_isResidualShift
-- name    : BooleanIsoperimetry.paperColexShiftMove_isResidualShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:09.236567+00:00
-- url     : https://prove2.me/theorems/d16cdb60-d1cb-4451-b92c-599e6af8e407
-- title:
--   Boolean Isoperimetry: paper Colex Shift Move is Residual Shift
-- statement:
--   Assemble the descent target from a pure within-layer colex move **and** the
--   separately supplied boundary non-increase `hnbhd`.  The boundary bound is genuine
--   selection data (from the KK existence leaf), not a projection off the move
--   predicate: `paperColexShiftMove_neighborhood_card_le` no longer exists because it
--   is false for arbitrary colex shifts (see the `IsPaperColexShiftMove` docstring).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1252-L1256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1252-L1256

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

theorem BooleanIsoperimetry.paperColexShiftMove_isResidualShift {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A')
    (hnbhd : (neighborhood 1 A').card ≤ (neighborhood 1 A).card) :
    IsDownFixedResidualShift A A' := by sorry
