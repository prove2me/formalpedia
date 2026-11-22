-- Prove2me | Theorems.Thm_BooleanIsoperimetry_disjoint_embeddedPair
-- name    : BooleanIsoperimetry.disjoint_embeddedPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:40.050689+00:00
-- url     : https://prove2.me/theorems/2e738825-f290-4677-914b-b69ffa31b205
-- title:
--   Boolean Isoperimetry: disjoint embedded Pair
-- statement:
--   The Boolean Isoperimetry construction uses the disjoint embedded Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L103-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L103-L111

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

theorem BooleanIsoperimetry.disjoint_embeddedPair {N : ℕ} (A B : Finset (Cube N)) :
    Disjoint (A.image embed0) (B.image embed1) := by sorry
