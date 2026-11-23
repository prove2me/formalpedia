-- Prove2me | Theorems.Thm_Apportionmentlib_Rule_le_seats
-- name    : Apportionmentlib.Rule.le_seats
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:41:27.917155+00:00
-- url     : https://prove2.me/theorems/865c4dd6-7449-4585-90e3-e4104648bcc4
-- title:
--   Rule: le seats
-- statement:
--   A quota rule allocates at least `m` seats to party `i` whenever its quota is at least `m`.
--
--   Source: https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Basic.lean#L196-L203
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Basic.lean#L196-L203

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Definitions.Def_Apportionmentlib_Basic
set_option autoImplicit false
@[expose] public section
public section
open BigOperators
open Apportionmentlib

theorem Apportionmentlib.Rule.le_seats (rule : Rule) [h_quota : IsQuotaRule rule] {n : ℕ} (election : Election n)
    (i : Fin n) (m : ℕ) (h : (m : ℚ) ≤ election.quota i) :
    ∀ App ∈ rule.res election, m ≤ App[i] := by sorry
