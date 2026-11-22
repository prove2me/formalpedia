-- Prove2me | Theorems.Thm_BooleanIsoperimetry_exists_fullyCompressed_le
-- name    : BooleanIsoperimetry.exists_fullyCompressed_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:39.809733+00:00
-- url     : https://prove2.me/theorems/080e4092-49df-4ad8-99a8-81331a9cdb93
-- title:
--   Boolean Isoperimetry: exists fully Compressed le
-- statement:
--   **Every family compresses to a fully-compressed family of the same size whose
--   unit neighborhood is no larger** — now via the honest Kruskal–Katona jump.  Reduce
--   `A` to a lower-saturated, Down-fixed `A₁` (coordinate-Down + level-block moves,
--   sorry-free), then replace `A₁` by the simplicial initial segment of its size; the
--   neighborhood does not increase by `simplicialInitSeg_neighborhood_le_of_lowerSaturated`
--   (whose crux is the mathlib theorem `Finset.kruskal_katona` via `upperLayerShadow_min`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2174-L2181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2174-L2181

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

theorem BooleanIsoperimetry.exists_fullyCompressed_le {N : ℕ} (A : Finset (Cube N)) :
    ∃ C : Finset (Cube N), IsFullyCompressed C ∧ C.card = A.card ∧
      (neighborhood 1 C).card ≤ (neighborhood 1 A).card := by sorry
