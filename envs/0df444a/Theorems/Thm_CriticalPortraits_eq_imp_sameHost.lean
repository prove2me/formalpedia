-- Prove2me | Theorems.Thm_CriticalPortraits_eq_imp_sameHost
-- name    : CriticalPortraits.eq_imp_sameHost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:07.003905+00:00
-- url     : https://prove2.me/theorems/74d834ef-1786-477c-9b07-d45e9326301a
-- title:
--   Critical Portraits: eq imp same Host
-- statement:
--   If two survivors coincide as points they share a host (Portrait disjointness).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L641-L648
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L641-L648

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.eq_imp_sameHost {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P) (hxy : x = y) :
    hostSet P x hx = hostSet P y hy := by sorry
