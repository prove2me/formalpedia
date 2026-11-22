-- Prove2me | Theorems.Thm_Egrs75_Probe_clearing_high
-- name    : Egrs75.Probe.clearing_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:00.537478+00:00
-- url     : https://prove2.me/theorems/d65f460e-3571-4667-b37c-f0b07a670017
-- title:
--   Probe: clearing high
-- statement:
--   **Clean branch of `egrs_clearing`: when `q^j > N`.**  If the top bad base-`q`
--   index `j` of `n` satisfies `q^j > N`, then a `LowDigits p` number drawn from the
--   window `[q^j, 2*q^j)` is `> N` and good at every base-`q` index `≥ j` — no carry
--   control needed.  KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ClearingHigh.lean#L55-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ClearingHigh.lean#L55-L64

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Probe
open Nat
open Egrs75
open Egrs75.RepairPaperfaithful

theorem Egrs75.Probe.clearing_high {p q : ℕ} (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q)
    (N : ℕ) {j : ℕ} (hjN : N < q ^ j) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, j ≤ i → ¬ BadAt q i n') := by sorry
