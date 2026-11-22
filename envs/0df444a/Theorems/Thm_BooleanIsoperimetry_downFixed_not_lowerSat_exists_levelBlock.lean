-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downFixed_not_lowerSat_exists_levelBlock
-- name    : BooleanIsoperimetry.downFixed_not_lowerSat_exists_levelBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:26.044953+00:00
-- url     : https://prove2.me/theorems/ece90857-55ae-41e8-b6d2-091b09b13ffb
-- title:
--   Boolean Isoperimetry: down Fixed not lower Sat exists level Block
-- statement:
--   **Terminalization core for lower-level-saturation failure.**
--
--   The previous singleton "near-miss" formulation was too strong: a down-closed
--   family can fail lower-level saturation because of an absent block `T` that differs
--   from every larger present block in several new coordinates.  The PDF-faithful
--   move is the full block replacement `U = S \ T`, `V = T \ S`, with `V.card <
--   U.card`.
--
--   This leaf is the remaining local terminalization content: from a coordinate
--   Down-fixed, non-lower-saturated family, select an admissible Frankl-Furedi level
--   block move.  It is intentionally a pure move statement; boundary monotonicity is
--   still proved from `IsPaperLevelBlockMove`, not bundled into the predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1845-L1871
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1845-L1871

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

theorem BooleanIsoperimetry.downFixed_not_lowerSat_exists_levelBlock {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (h : ¬ IsLowerLevelSaturated A) :
    ∃ U V, IsPaperLevelBlockMove A (familyUp U V A) U V := by sorry
