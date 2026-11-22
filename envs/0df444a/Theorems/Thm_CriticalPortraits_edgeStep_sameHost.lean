-- Prove2me | Theorems.Thm_CriticalPortraits_edgeStep_sameHost
-- name    : CriticalPortraits.edgeStep_sameHost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:56.640182+00:00
-- url     : https://prove2.me/theorems/7d7cadb8-0dd7-4d66-9d21-41dbe4a8967f
-- title:
--   Critical Portraits: edge Step same Host
-- statement:
--   An `edgeStep` keeps you in the same host (the predecessor lives in the same block).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L879-L887
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L879-L887

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

theorem CriticalPortraits.edgeStep_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u v : ZMod (d * m)} (hstep : edgeStep P u v) (hu : u ∈ T P) (hv : v ∈ T P) :
    hostSet P u hu = hostSet P v hv := by sorry
