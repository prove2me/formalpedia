-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_shadow_subset
-- name    : BooleanIsoperimetry.familyUp_shadow_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:59.833136+00:00
-- url     : https://prove2.me/theorems/1e4509b3-7fc2-4731-b820-89ac65b96dc2
-- title:
--   Boolean Isoperimetry: family Up shadow subset
-- statement:
--   The Boolean Isoperimetry construction uses the family Up shadow subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1084-L1095
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1084-L1095

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

theorem BooleanIsoperimetry.familyUp_shadow_subset {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV : IsUVAdmissibleForFamily A U V) :
    shadow (familyUp U V A) ⊆ familyUp U V (shadow A) := by sorry
