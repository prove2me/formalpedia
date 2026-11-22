-- Prove2me | Theorems.Thm_Egrs75_SmokeProbe_egrs_3_7
-- name    : Egrs75.SmokeProbe.egrs_3_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:28.58967+00:00
-- url     : https://prove2.me/theorems/dda4954a-61e2-4071-aac1-61a6200bfce4
-- title:
--   Smoke Probe: egrs 3 7
-- statement:
--   Infinitely many `n` with `3 ∤ C(2n,n)` and `7 ∤ C(2n,n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Instances.lean#L36-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Instances.lean#L36-L37

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

theorem Egrs75.SmokeProbe.egrs_3_7 : {n : ℕ | ¬ 3 ∣ Nat.centralBinom n ∧ ¬ 7 ∣ Nat.centralBinom n}.Infinite := by sorry
