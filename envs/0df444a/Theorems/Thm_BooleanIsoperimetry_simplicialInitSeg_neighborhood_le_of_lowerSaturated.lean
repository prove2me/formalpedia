-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_neighborhood_le_of_lowerSaturated
-- name    : BooleanIsoperimetry.simplicialInitSeg_neighborhood_le_of_lowerSaturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:34.830789+00:00
-- url     : https://prove2.me/theorems/fe4cb6b7-52da-40ef-b2a4-8ea8dfd06b1f
-- title:
--   Boolean Isoperimetry: simplicial Init Seg neighborhood le of lower Saturated
-- statement:
--   **Lower-saturated KK-jump.**  For a lower-level-saturated family `A`, the
--   simplicial initial segment of size `A.card` has unit neighborhood no larger than
--   `A`'s.  Proof: `A` is a full ball below its top layer `r` plus a card-`r` slice
--   `L`; the initial segment shares that ball and carries the *colex-initial* `r`-slice
--   `layerInitSeg N r |L|`, whose upper shadow is minimal by the Kruskal–Katona
--   theorem `upperLayerShadow_min`.  `neighborhood_card_le_of_layers_upperShadow_le`
--   then transfers the layer bound to the full neighborhood.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2013-L2102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2013-L2102

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

theorem BooleanIsoperimetry.simplicialInitSeg_neighborhood_le_of_lowerSaturated {N : ℕ} {A : Finset (Cube N)}
    (hl : IsLowerLevelSaturated A) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by sorry
