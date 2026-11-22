-- Prove2me | Theorems.Thm_CriticalPortraits_column_sep_geom_dir
-- name    : CriticalPortraits.column_sep_geom_dir
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:40.84392+00:00
-- url     : https://prove2.me/theorems/c3f8eee7-c910-4f9d-9743-a8ffc2dcca08
-- title:
--   Critical Portraits: column sep geom dir
-- statement:
--   **Geometric DIRECTIONAL COLUMN-SEPARATION.**  Exposes the gap level and the run-direction
--       columns at the survivor family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L531-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L531-L544

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

theorem CriticalPortraits.column_sep_geom_dir [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) (hwin : loV P e < hiV e) :
    ∃ g, loV P e < g ∧ g ≤ hiV e ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        ¬ (loV P r < g ∧ g ≤ hiV r)) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        hiV r < g → colV e < colV r) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        g ≤ loV P r → colV r < colV e) := by sorry
