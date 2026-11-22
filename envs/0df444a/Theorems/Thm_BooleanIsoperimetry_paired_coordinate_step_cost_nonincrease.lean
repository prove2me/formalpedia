-- Prove2me | Theorems.Thm_BooleanIsoperimetry_paired_coordinate_step_cost_nonincrease
-- name    : BooleanIsoperimetry.paired_coordinate_step_cost_nonincrease
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:38.439654+00:00
-- url     : https://prove2.me/theorems/3cf700af-0a5c-4818-bb17-a0866f5c4c95
-- title:
--   Boolean Isoperimetry: paired coordinate step cost nonincrease
-- statement:
--   One paired coordinate Up/Down compression does not increase the two-slice
--   Frankl-Füredi cost.
--
--   This is now a **sorry-free reduction** to the two named PDF shadow-monotonicity
--   lemmas above: the slice cardinalities are preserved by the compression
--   (`hA.1`, `hB.1`), and `max` is monotone in its first argument, so the cost bound
--   follows term-by-term from `|N(A')| ≤ |N(A)|` and `|N(B')| ≤ |N(B)|`.  No scalar
--   Harper minimization is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L287-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L287-L301

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

theorem BooleanIsoperimetry.paired_coordinate_step_cost_nonincrease {N : ℕ} {A B A' B' : Finset (Cube N)}
    {i : Fin N} (hA : IsCoordinateUp i A A') (hB : IsCoordinateDown i B B') :
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by sorry
