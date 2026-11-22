-- Prove2me | Theorems.Thm_CriticalPortraits_reach_sameHost
-- name    : CriticalPortraits.reach_sameHost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:59.979048+00:00
-- url     : https://prove2.me/theorems/dc47ea9d-db34-4628-ae2a-a63002805002
-- title:
--   Critical Portraits: reach same Host
-- statement:
--   Survivors reachable from `x` by `edgeStep` share `x`'s host.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L896-L906
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L896-L906

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

theorem CriticalPortraits.reach_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P)
    (hreach : Relation.ReflTransGen (edgeStep P) x z) (hz : z ∈ T P) :
    hostSet P z hz = hostSet P x hx := by sorry
