-- Prove2me | Theorems.Thm_CriticalPortraits_hostSet_predIn
-- name    : CriticalPortraits.hostSet_predIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:57.61229+00:00
-- url     : https://prove2.me/theorems/71a01a19-5d1e-4117-9434-43dcd6065ec8
-- title:
--   Critical Portraits: host Set pred In
-- statement:
--   For a survivor `u` whose predecessor is itself a survivor, they share a host.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L890-L893
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L890-L893

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

theorem CriticalPortraits.hostSet_predIn [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u : ZMod (d * m)} (hu : u ∈ T P) (hpu : predIn P u hu ∈ T P) :
    hostSet P (predIn P u hu) hpu = hostSet P u hu := by sorry
