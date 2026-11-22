-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_vertex_iso
-- name    : BooleanIsoperimetry.harper_vertex_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:45.189805+00:00
-- url     : https://prove2.me/theorems/ea436d50-6b09-48c7-8682-e566f49b0550
-- title:
--   Boolean Isoperimetry: harper vertex iso
-- statement:
--   **Harper's vertex-isoperimetric theorem (master form).**  For *every* finite
--   family `A` of vertices of the `N`-cube, the simplicial initial segment of the
--   same size has a closed `1`-neighbourhood no larger than `A`'s; equivalently the
--   boundary function `H N A.card` lower-bounds `(neighborhood 1 A).card`.
--
--   This is the Frankl–Füredi/PDF master statement, generalising the initial-segment
--   identity `H` to arbitrary families.  It is proved here by the standard
--   slice induction on `N`: `neighborhood_succ` decomposes the boundary across the
--   two coordinate slices, the induction hypothesis bounds each slice, and the single
--   cross-slice crux is `harper_split_min`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L331-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L331-L373

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.harper_vertex_iso (N : ℕ) (A : Finset (Cube N)) :
    H N A.card ≤ (neighborhood 1 A).card := by sorry
