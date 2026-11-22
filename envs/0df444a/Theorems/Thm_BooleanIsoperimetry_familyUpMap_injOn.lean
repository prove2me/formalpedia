-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUpMap_injOn
-- name    : BooleanIsoperimetry.familyUpMap_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:45.71235+00:00
-- url     : https://prove2.me/theorems/14083488-bc80-4f47-8b89-280b157f57b5
-- title:
--   Boolean Isoperimetry: family Up Map inj On
-- statement:
--   The paper's `𝒰` is one-to-one on its family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L374-L392
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L374-L392

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

theorem BooleanIsoperimetry.familyUpMap_injOn {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    Set.InjOn (familyUpMap U V 𝒜) ↑𝒜 := by sorry
