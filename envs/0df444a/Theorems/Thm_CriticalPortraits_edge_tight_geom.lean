-- Prove2me | Theorems.Thm_CriticalPortraits_edge_tight_geom
-- name    : CriticalPortraits.edge_tight_geom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:00.255036+00:00
-- url     : https://prove2.me/theorems/5bf1d607-a6ab-4f6a-b977-5531819174fc
-- title:
--   Critical Portraits: edge tight geom
-- statement:
--   **Geometric TIGHTNESS (g(e) = h(e) - 1).** Every survivor edge `e` has a saturated own
--       window: `N(loV e, hiV e) = hiV e - loV e`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L504-L514
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L504-L514

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

theorem CriticalPortraits.edge_tight_geom [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) :
    AbstractLaminar.N (survivorFamily hd hm hP) (loV P e) (hiV e)
      = hiV e - loV P e := by sorry
