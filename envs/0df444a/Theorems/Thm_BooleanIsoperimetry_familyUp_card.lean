-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_card
-- name    : BooleanIsoperimetry.familyUp_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:42.60759+00:00
-- url     : https://prove2.me/theorems/c44a1c5d-5d24-48f3-ad8d-323c3dde91ba
-- title:
--   Boolean Isoperimetry: family Up card
-- statement:
--   **Cardinality preservation for `𝒰`** (`|𝒰(𝒜)| = |𝒜|`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L416-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L416-L418

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

theorem BooleanIsoperimetry.familyUp_card {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    (familyUp U V 𝒜).card = 𝒜.card := by sorry
