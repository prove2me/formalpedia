-- Prove2me | Theorems.Thm_Egrs75_MathlibAPI_irrational_log_div_log
-- name    : Egrs75.MathlibAPI.irrational_log_div_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:30.720865+00:00
-- url     : https://prove2.me/theorems/d9eb9ec6-26c4-417f-99e9-5fe61e6e126e
-- title:
--   Mathlib API: irrational log div log
-- statement:
--   **(A) — irrationality of `log p / log q`** for distinct primes `p q`.
--   KERNEL-CLEAN. This is the Mathlib-missing fact; everything in the dense-orbit
--   route hangs off it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L96-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L96-L141

module
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MathlibAPI
open Nat
open Egrs75

theorem Egrs75.MathlibAPI.irrational_log_div_log {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Irrational (Real.log p / Real.log q) := by sorry
