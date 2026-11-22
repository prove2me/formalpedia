-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_pow_lowPDigitIndex_dvd
-- name    : Egrs75.ClearingP3.pow_lowPDigitIndex_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:24.200416+00:00
-- url     : https://prove2.me/theorems/2036b458-b599-42b5-8b2e-fb487ab86fa6
-- title:
--   Clearing P3: pow low PDigit Index dvd
-- statement:
--   For `1 < p` and `n ≠ 0`, `p ^ (lowPDigitIndex p n) ∣ n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L90-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L90-L93

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP3.pow_lowPDigitIndex_dvd {p n : ℕ} (_hp : 1 < p) (_hn : n ≠ 0) :
    p ^ (lowPDigitIndex p n) ∣ n := by sorry
