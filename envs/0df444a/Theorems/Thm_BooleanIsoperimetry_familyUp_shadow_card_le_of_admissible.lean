-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_shadow_card_le_of_admissible
-- name    : BooleanIsoperimetry.familyUp_shadow_card_le_of_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:58.115425+00:00
-- url     : https://prove2.me/theorems/c1b7c0fd-8f7f-4790-b1fa-c00ddd0f6777
-- title:
--   Boolean Isoperimetry: family Up shadow card le of admissible
-- statement:
--   **Block move does not increase the shadow** (Frankl–Füredi / Kruskal–Katona).
--   For disjoint admissible blocks the `𝒰`-move's shadow is no larger than the
--   original's.  This is the mathlib UV-compression shadow bound
--   `Finset.UV.card_shadow_compression_le` transported across the block dictionary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L816-L828
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L816-L828

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

theorem BooleanIsoperimetry.familyUp_shadow_card_le_of_admissible {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV : IsUVAdmissibleForFamily A U V) :
    (familyUp U V A).shadow.card ≤ A.shadow.card := by sorry
