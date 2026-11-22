-- Prove2me | Theorems.Thm_Egrs75_SmokeProbe_egrs_3_5
-- name    : Egrs75.SmokeProbe.egrs_3_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:42.925212+00:00
-- url     : https://prove2.me/theorems/c8e46f2d-3f00-4eea-b0c9-c39f30337a7a
-- title:
--   Smoke Probe: egrs 3 5
-- statement:
--   Infinitely many `n` with `3 ∤ C(2n,n)` and `5 ∤ C(2n,n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Instances.lean#L32-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Instances.lean#L32-L33

module
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Prime.Defs
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_Egrs75_Instances
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SmokeProbe
open Egrs75.MuFinish

theorem Egrs75.SmokeProbe.egrs_3_5 : {n : ℕ | ¬ 3 ∣ Nat.centralBinom n ∧ ¬ 5 ∣ Nat.centralBinom n}.Infinite := by sorry
