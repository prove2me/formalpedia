-- Prove2me | Theorems.Thm_BooleanIsoperimetry_tailCount_succ_slice
-- name    : BooleanIsoperimetry.tailCount_succ_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:23.849032+00:00
-- url     : https://prove2.me/theorems/a365a0be-d57b-4e9d-a0fd-eb6d459c83a2
-- title:
--   Boolean Isoperimetry: tail Count succ slice
-- statement:
--   The Boolean Isoperimetry construction uses the tail Count succ slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L382-L417
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L382-L417

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset

theorem BooleanIsoperimetry.tailCount_succ_slice {N : ℕ} (k : ℕ) (A : Finset (Cube (N + 1))) :
    (A.filter (fun z => k ≤ z.card)).card
      = ((slice0 A).filter (fun z => k ≤ z.card)).card
        + ((slice1 A).filter (fun z => k - 1 ≤ z.card)).card := by sorry
