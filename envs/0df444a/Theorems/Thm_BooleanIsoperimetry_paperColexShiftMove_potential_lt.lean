-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperColexShiftMove_potential_lt
-- name    : BooleanIsoperimetry.paperColexShiftMove_potential_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:09.106838+00:00
-- url     : https://prove2.me/theorems/55ca7045-0449-40f1-86f1-0fd0b511cc91
-- title:
--   Boolean Isoperimetry: paper Colex Shift Move potential lt
-- statement:
--   Rank-potential strict descent for a pure within-layer colex move.  This is a
--   genuine dictionary consequence of the move (`swap_potential_lt` for a single
--   colex swap, `paperColexBlockMove_potential_lt` for a block move) — no boundary or
--   KK input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1240-L1245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1240-L1245

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

theorem BooleanIsoperimetry.paperColexShiftMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A') : compressionPotential A' < compressionPotential A := by sorry
