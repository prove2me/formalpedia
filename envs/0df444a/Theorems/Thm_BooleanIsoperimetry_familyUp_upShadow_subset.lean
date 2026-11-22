-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_upShadow_subset
-- name    : BooleanIsoperimetry.familyUp_upShadow_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:05.187087+00:00
-- url     : https://prove2.me/theorems/4caef52c-ba17-43ca-95df-04d70c9cd14a
-- title:
--   Boolean Isoperimetry: family Up up Shadow subset
-- statement:
--   The Boolean Isoperimetry construction uses the family Up up Shadow subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1097-L1107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1097-L1107

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

theorem BooleanIsoperimetry.familyUp_upShadow_subset {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    upShadow (familyUp U V A) ⊆ familyUp U V (upShadow A) := by sorry
