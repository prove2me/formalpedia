-- Prove2me | Theorems.Thm_Egrs75_RepairDV_lowDigits_disjoint_add
-- name    : Egrs75.RepairDV.lowDigits_disjoint_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:04.187653+00:00
-- url     : https://prove2.me/theorems/d636bd20-5245-4742-bcfb-5853f00005ce
-- title:
--   Repair DV: low Digits disjoint add
-- statement:
--   **Disjoint-support `LowDigits p` addition (KERNEL-CLEAN).**  If `U < p^k` and both
--   `U` and `Hi` are `LowDigits p` (and `Hi > 0`, `p ≥ 2`), then `U + p^k · Hi` is
--   `LowDigits p`: its base-`p` digits are exactly those of `U`, of `Hi`, and padding
--   zeros, all `≤ (p-1)/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L112-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L112-L126

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction

theorem Egrs75.RepairDV.lowDigits_disjoint_add {p k U Hi : ℕ} (hp : 1 < p) (hU : U < p ^ k) (hHi : 0 < Hi)
    (hUlow : LowDigits p U) (hHilow : LowDigits p Hi) : LowDigits p (U + p ^ k * Hi) := by sorry
