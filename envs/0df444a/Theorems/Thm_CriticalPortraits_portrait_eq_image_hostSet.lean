-- Prove2me | Theorems.Thm_CriticalPortraits_portrait_eq_image_hostSet
-- name    : CriticalPortraits.portrait_eq_image_hostSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:37.399065+00:00
-- url     : https://prove2.me/theorems/1d17f5f9-7c4b-4d6e-90e9-9fe1c39150fe
-- title:
--   Critical Portraits: portrait eq image host Set
-- statement:
--   **`P` is recovered as the image of its survivors' host sets.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L444-L466
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L444-L466

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.portrait_eq_image_hostSet {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    P = (T P).attach.image (fun x => hostSet P x.1 x.2) := by sorry
