-- Prove2me | Theorems.Thm_Egrs75_Probe_good_above_of_mem_window
-- name    : Egrs75.Probe.good_above_of_mem_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:01.598329+00:00
-- url     : https://prove2.me/theorems/3f11b935-2440-4a6e-bf1d-1d058b886768
-- title:
--   Probe: good above of mem window
-- statement:
--   Goodness of the high block: if `q^j ≤ m < 2*q^j` and `q ≥ 3`, then every base-`q`
--   digit of `m` at index `≥ j` is `≤ (q-1)/2` (digit at `j` is `1`, digits above are `0`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ClearingHigh.lean#L30-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ClearingHigh.lean#L30-L49

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

theorem Egrs75.Probe.good_above_of_mem_window {q j m : ℕ} (hq : 3 ≤ q)
    (hlo : q ^ j ≤ m) (hhi : m < 2 * q ^ j) :
    ∀ i, j ≤ i → m / q ^ i % q ≤ (q - 1) / 2 := by sorry
