-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_split_reaches_canonical
-- name    : BooleanIsoperimetry.cascade_split_reaches_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:45.854089+00:00
-- url     : https://prove2.me/theorems/7cdd2abd-2619-4145-89dd-2645d478ae7b
-- title:
--   Boolean Isoperimetry: cascade split reaches canonical
-- statement:
--   **Phase-3 cascade exchange (sorry-free).**
--
--   A pair of simplicial initial segments `(simplicialInitSeg N a, simplicialInitSeg N b)`
--   of total `a + b` can be compressed across the top coordinate to *the* canonical
--   cascade pair `(simplicialInitSeg N p, simplicialInitSeg N q)` of the same total,
--   without increasing the two-slice boundary cost.
--
--   The proof embeds both pairs into the `(N + 1)`-cube via `embeddedPair`, where the
--   two-slice cost becomes a plain neighborhood size; the canonical pair embeds to the
--   simplicial initial segment of size `a + b` (`embeddedPair_eq_of_slice_eq`), so the
--   cost comparison is exactly the dimension-`(N + 1)` Harper minimality
--   `simplicialInitSeg_neighborhood_card_min`.
--
--   The existence/total parts are immediate from the chosen canonical witnesses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2507-L2555
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2507-L2555

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

theorem BooleanIsoperimetry.cascade_split_reaches_canonical {N : ℕ} (a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = a + b ∧
      PairShadowCost N A' B'
        ≤ PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) := by sorry
