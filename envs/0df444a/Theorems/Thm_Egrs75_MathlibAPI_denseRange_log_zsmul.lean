-- Prove2me | Theorems.Thm_Egrs75_MathlibAPI_denseRange_log_zsmul
-- name    : Egrs75.MathlibAPI.denseRange_log_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:33.859228+00:00
-- url     : https://prove2.me/theorems/2781bc10-ccbd-4cc2-8179-c85e99600d6e
-- title:
--   Mathlib API: dense Range log zsmul
-- statement:
--   **(B) — the dense orbit** `{k · log p mod log q}` for distinct primes `p q`.
--   KERNEL-CLEAN. `AddCircle.denseRange_zsmul_coe_iff` ∘ (A). The base-`q` top block of
--   `p^k` can be steered into any window for arbitrarily large `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L153-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L153-L157

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

theorem Egrs75.MathlibAPI.denseRange_log_zsmul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    DenseRange (· • Real.log p : ℤ → AddCircle (Real.log q)) := by sorry
