-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_potential_lt_of_blockLt
-- name    : BooleanIsoperimetry.familyUp_potential_lt_of_blockLt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:59.749915+00:00
-- url     : https://prove2.me/theorems/313c8a92-d1a5-48f4-91a4-ebd6f5126c15
-- title:
--   Boolean Isoperimetry: family Up potential lt of block Lt
-- statement:
--   **Block-move potential descent (general).**  If every replaced set drops in the
--   simplicial order, then a nontrivial `familyUp U V` move (`familyUp U V A ≠ A`) strictly
--   decreases the rank potential `compressionPotential = ∑ rank`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L707-L739
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L707-L739

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

theorem BooleanIsoperimetry.familyUp_potential_lt_of_blockLt {N : ℕ} {U V : Cube N} {A : Finset (Cube N)}
    (hne : familyUp U V A ≠ A)
    (hlt : ∀ S, U ⊆ S → Disjoint V S → simplicialLt (blockReplace U V S) S) :
    compressionPotential (familyUp U V A) < compressionPotential A := by sorry
