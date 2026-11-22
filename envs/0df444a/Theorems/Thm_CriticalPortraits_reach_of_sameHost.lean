-- Prove2me | Theorems.Thm_CriticalPortraits_reach_of_sameHost
-- name    : CriticalPortraits.reach_of_sameHost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:56.959423+00:00
-- url     : https://prove2.me/theorems/8f6ca3ba-6c02-4a10-8de6-33b37bca32f8
-- title:
--   Critical Portraits: reach of same Host
-- statement:
--   Two survivors in the same host reach the SAME bottom survivor; hence are mutually reachable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L926-L956
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L926-L956

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

theorem CriticalPortraits.reach_of_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P) (hz : z ∈ T P)
    (hhost : hostSet P z hz = hostSet P x hx) :
    Relation.ReflTransGen (edgeStep P) z x := by sorry
