-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_simplicialInitSeg_eq_cascadeSplit
-- name    : BooleanIsoperimetry.slice1_simplicialInitSeg_eq_cascadeSplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:14.313884+00:00
-- url     : https://prove2.me/theorems/850a49a7-3c09-4831-8c11-19c287bfddd2
-- title:
--   Boolean Isoperimetry: slice1 simplicial Init Seg eq cascade Split
-- statement:
--   The Boolean Isoperimetry construction uses the slice1 simplicial Init Seg eq cascade Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2426-L2428
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2426-L2428

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

theorem BooleanIsoperimetry.slice1_simplicialInitSeg_eq_cascadeSplit {N x p q : ℕ} (h : CascadeSplit N x p q) :
    slice1 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N q := by sorry
