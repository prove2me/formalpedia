-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_one_subset_familyUp_neighborhood_of_admissible
-- name    : BooleanIsoperimetry.neighborhood_one_subset_familyUp_neighborhood_of_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:07.522537+00:00
-- url     : https://prove2.me/theorems/34716cf0-da03-448c-902d-b80dc49e23cf
-- title:
--   Boolean Isoperimetry: neighborhood one subset family Up neighborhood of admissible
-- statement:
--   **Closed unit-neighborhood compression inclusion.**
--   If a block move is doubly admissible for `A`, the neighborhood of the compressed
--   family is a subset of the compression of the neighborhood. This avoids layer-by-layer
--   bounds which are false when `|V| < |U|`, instead providing a global inclusion that
--   preserves cardinality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1114-L1144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1114-L1144

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

theorem BooleanIsoperimetry.neighborhood_one_subset_familyUp_neighborhood_of_admissible {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    neighborhood 1 (familyUp U V A) ⊆ familyUp U V (neighborhood 1 A) := by sorry
