-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyDown_card
-- name    : BooleanIsoperimetry.familyDown_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:40.889524+00:00
-- url     : https://prove2.me/theorems/7217a1c4-8215-4de8-b14a-972777d5f8c4
-- title:
--   Boolean Isoperimetry: family Down card
-- statement:
--   **Cardinality preservation for `𝒟`** (`|𝒟(ℬ)| = |ℬ|`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L421-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L421-L423

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

theorem BooleanIsoperimetry.familyDown_card {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    (familyDown U V ℬ).card = ℬ.card := by sorry
