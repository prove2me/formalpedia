-- Prove2me | Theorems.Thm_CriticalPortraits_column_sep_geom
-- name    : CriticalPortraits.column_sep_geom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:00.537736+00:00
-- url     : https://prove2.me/theorems/73c0eaa9-29e8-4f4b-8dd1-cbb7682b5b90
-- title:
--   Critical Portraits: column sep geom
-- statement:
--   **Geometric COLUMN-SEPARATION.** For a survivor edge `e` with a nondegenerate own window,
--       every maximal nested tile (root of `(loV e, hiV e]`) has column `≠ colV e`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L518-L527
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L518-L527

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

theorem CriticalPortraits.column_sep_geom [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) (hwin : loV P e < hiV e) :
    ∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
      colV r ≠ colV e := by sorry
