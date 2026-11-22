-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUpMap_compl
-- name    : BooleanIsoperimetry.familyUpMap_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:56.92989+00:00
-- url     : https://prove2.me/theorems/7f153305-dc20-4867-8455-d2a8625abf8f
-- title:
--   Boolean Isoperimetry: family Up Map compl
-- statement:
--   The per-set `𝒰`-map intertwines with complementation: applying `familyUpMap U V A`
--   then complementing equals complementing then applying the swapped map
--   `familyUpMap V U (Aᶜˢ)`.  (The membership guard `∉ A` becomes `∉ Aᶜˢ` under the
--   complement bijection.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L857-L879
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L857-L879

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

theorem BooleanIsoperimetry.familyUpMap_compl {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    (A : Finset (Cube N)) (S : Cube N) :
    (familyUpMap U V A S)ᶜ = familyUpMap V U (Aᶜˢ) Sᶜ := by sorry
