-- Prove2me | Theorems.Thm_Egrs75_SeedWindow_exists_small_step
-- name    : Egrs75.SeedWindow.exists_small_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:54.106686+00:00
-- url     : https://prove2.me/theorems/787bec21-bb65-489f-9b34-ba5a384f2df6
-- title:
--   Seed Window: exists small step
-- statement:
--   **Small-step lemma (KERNEL-CLEAN).**  For distinct primes `p q` and any
--   `ε > 0` there are naturals `a ≥ 1`, `b` with `δ := a·log p − b·log q` NONZERO,
--   `|δ| < ε`, and `b ≥ 1` whenever `δ < 0`.  Dirichlet supplies the approximation;
--   the kernel-clean `irrational_log_div_log` rules out `δ = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L99-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L99-L178

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75

theorem Egrs75.SeedWindow.exists_small_step {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℕ, 1 ≤ a ∧
      (a : ℝ) * Real.log p - (b : ℝ) * Real.log q ≠ 0 ∧
      |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| < ε ∧
      ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q < 0 → 1 ≤ b) := by sorry
