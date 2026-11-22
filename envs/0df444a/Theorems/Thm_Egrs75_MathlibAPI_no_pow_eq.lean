-- Prove2me | Theorems.Thm_Egrs75_MathlibAPI_no_pow_eq
-- name    : Egrs75.MathlibAPI.no_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:31.367309+00:00
-- url     : https://prove2.me/theorems/0d392eb8-ef45-4dfd-a6b2-4d094ea834f6
-- title:
--   Mathlib API: no pow eq
-- statement:
--   **Core arithmetic obstruction.** For distinct primes `p q` there are no
--   positive naturals `n m` with `(p:ℝ)^n = (q:ℝ)^m`. (Equivalently `p^n = q^m` in `ℕ`
--   is impossible.) This is the unique-factorisation fact behind `log p / log q ∉ ℚ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L80-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LogIrrationality.lean#L80-L91

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

theorem Egrs75.MathlibAPI.no_pow_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {n m : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ n ≠ (q : ℝ) ^ m := by sorry
