-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_neighborhood_card_min
-- name    : BooleanIsoperimetry.simplicialInitSeg_neighborhood_card_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:12.170301+00:00
-- url     : https://prove2.me/theorems/c63bf237-bd78-4197-9d3b-0f0aa297da89
-- title:
--   Boolean Isoperimetry: simplicial Init Seg neighborhood card min
-- statement:
--   **Single-family vertex isoperimetry (dimension `N`), via compression.**  The
--   simplicial initial segment of size `A.card` has the smallest unit neighborhood
--   among all families of that size.  This is `H N A.card ≤ |N A|` in unfolded form.
--
--   It is proved here *independently of the scalar Macaulay route*: by compressing `A`
--   to a fully-compressed family `C` (`exists_fullyCompressed_le`, boundary
--   non-increasing), which by `fullyCompressed_eq_initSeg` is the simplicial initial
--   segment of size `C.card = A.card`.  It does NOT use `harper_compression_descent`
--   or `harper_macaulay_min` (both downstream of this file).  The compression bottoms
--   out at the honest Kruskal–Katona jump: `exists_fullyCompressed_le` reduces `A` to
--   a lower-saturated, Down-fixed family (coordinate-Down + level-block moves) and
--   then replaces its top slice by the colex-initial segment, whose upper shadow is
--   minimal by mathlib's `Finset.kruskal_katona` (`upperLayerShadow_min`).  This
--   replaced the earlier single-swap colex descent, whose selection leaf
--   (`exists_colex_swap_upperLayerShadow_le_of_layerUpShifted`) was **false** —
--   up-shifted-but-not-colex-initial layers are stuck under single swaps
--   (`verify_colex_singlelayer_false_small.py`), so the Kruskal–Katona jump to the
--   whole initial segment is essential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2201-L2206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2201-L2206

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

theorem BooleanIsoperimetry.simplicialInitSeg_neighborhood_card_min {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by sorry
