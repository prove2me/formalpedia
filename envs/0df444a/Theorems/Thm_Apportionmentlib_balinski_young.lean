-- Prove2me | Theorems.Thm_Apportionmentlib_balinski_young
-- name    : Apportionmentlib.balinski_young
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:41:24.70236+00:00
-- url     : https://prove2.me/theorems/4b735378-bda3-427f-a691-6dce2259a44b
-- title:
--   Apportionmentlib: balinski young
-- statement:
--   Balinski-Young impossibility theorem: a quota rule is never population monotone, so no
--   apportionment method can satisfy both properties simultaneously. Anonymity is not assumed (nor any
--   other property).
--
--   Gölz, Peters and Procaccia [GoelzPetersProcaccia2025] prove this for five or more parties, leaving
--   four open in this generality; the witness used here has only four parties, settling that case.
--
--   Source: https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Basic.lean#L335-L411
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Basic.lean#L335-L411

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
variable (rule : Rule) {a b c : ℕ} {App : Apportionment 4}
variable [IsQuotaRule rule]

theorem Apportionmentlib.balinski_young : ¬IsPopulationMonotone rule := by sorry
