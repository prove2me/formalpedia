-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_isResidualShift
-- name    : BooleanIsoperimetry.paperColexBlockMove_isResidualShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:38.024932+00:00
-- url     : https://prove2.me/theorems/b5dbcdae-df13-489d-9e73-3bae63296995
-- title:
--   Boolean Isoperimetry: paper Colex Block Move is Residual Shift
-- statement:
--   The Boolean Isoperimetry construction uses the paper Colex Block Move is Residual Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1223-L1228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1223-L1228

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

theorem BooleanIsoperimetry.paperColexBlockMove_isResidualShift {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j)
    (_hdown : IsCoordinateDownFixed A)
    (_hlower : IsLowerLevelSaturated A) : IsDownFixedResidualShift A A' := by sorry
