-- Prove2me | Theorems.Thm_Egrs75_SeedWindow_seed_window
-- name    : Egrs75.SeedWindow.seed_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:51.611297+00:00
-- url     : https://prove2.me/theorems/8974ad02-7030-4694-9442-757e90aab7f0
-- title:
--   Seed Window: seed window
-- statement:
--   **THE DIOPHANTINE SEED (KERNEL-CLEAN).**  For distinct primes `p q` with
--   `q ≥ 3` and any floor `F`, there are `α ≥ 1` and `e` with `q^(e+3) > F` and
--
--       (q-1)/2 · q^(e+3)  <  p^α   and   4·p^α < 4·((q-1)/2 · q^(e+3)) + q^(e+1).
--
--   So `p^α` (automatically `LowDigits p`) has base-`q` digit `(q-1)/2` at `e+3`,
--   digit `0` at `e+2`, zeros above `e+3`, and excess `< q^(e+1)` — the EGRS75
--   condition-(2) staircase seed at arbitrary height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L190-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L190-L322

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

theorem Egrs75.SeedWindow.seed_window {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq3 : 3 ≤ q)
    (hpq : p ≠ q) (F : ℕ) :
    ∃ α e : ℕ, 1 ≤ α ∧ F < q ^ (e + 3) ∧
      (q - 1) / 2 * q ^ (e + 3) < p ^ α ∧
      4 * p ^ α < 4 * ((q - 1) / 2 * q ^ (e + 3)) + q ^ (e + 1) := by sorry
