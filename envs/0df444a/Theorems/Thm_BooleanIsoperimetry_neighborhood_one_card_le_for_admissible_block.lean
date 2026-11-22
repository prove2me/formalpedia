-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_one_card_le_for_admissible_block
-- name    : BooleanIsoperimetry.neighborhood_one_card_le_for_admissible_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:00.208715+00:00
-- url     : https://prove2.me/theorems/ed1fea42-30ba-4d0a-8805-6cacd6732d10
-- title:
--   Boolean Isoperimetry: neighborhood one card le for admissible block
-- statement:
--   **Closed unit-neighborhood nonincrease for a doubly-admissible block move.**
--   This is the genuine Frankl–Füredi boundary-monotonicity leaf: an admissible
--   disjoint block `𝒰`-move that is admissible in *both* directions (primal
--   `IsUVAdmissibleForFamily A U V`, controlling the lower shadow, and dual
--   `IsUVAdmissibleForFamily (Aᶜˢ) V U`, controlling the upper shadow) does not
--   increase the closed unit neighborhood `neighborhood 1 A`.
--
--   It is proved via the global inclusion `neighborhood_one_subset_familyUp_neighborhood_of_admissible`,
--   avoiding false layer-by-layer bounds for moves where `|V| < |U|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1155-L1164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1155-L1164

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

theorem BooleanIsoperimetry.neighborhood_one_card_le_for_admissible_block {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    (neighborhood 1 (familyUp U V A)).card ≤ (neighborhood 1 A).card := by sorry
