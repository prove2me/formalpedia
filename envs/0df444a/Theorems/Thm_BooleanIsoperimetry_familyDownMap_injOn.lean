-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyDownMap_injOn
-- name    : BooleanIsoperimetry.familyDownMap_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:39.266802+00:00
-- url     : https://prove2.me/theorems/9af03fcb-127a-47e1-83e9-3a71e757ac42
-- title:
--   Boolean Isoperimetry: family Down Map inj On
-- statement:
--   The paper's `𝒟` is one-to-one on its family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L395-L413
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L395-L413

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

theorem BooleanIsoperimetry.familyDownMap_injOn {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    Set.InjOn (familyDownMap U V ℬ) ↑ℬ := by sorry
