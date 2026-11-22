-- Prove2me | Theorems.Thm_BooleanIsoperimetry_blockReplace_recover
-- name    : BooleanIsoperimetry.blockReplace_recover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:49.218963+00:00
-- url     : https://prove2.me/theorems/fbf0c7d5-8f51-4de9-a614-24b8919bf423
-- title:
--   Boolean Isoperimetry: block Replace recover
-- statement:
--   **Block recovery.**  When `U ⊆ S` and `V` is disjoint from `S`, the inverse
--   move `· - V + U` undoes `blockReplace U V`.  This is what makes the paper's `𝒰`
--   one-to-one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L335-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L335-L351

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

theorem BooleanIsoperimetry.blockReplace_recover {N : ℕ} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) :
    (blockReplace U V S \ V) ∪ U = S := by sorry
