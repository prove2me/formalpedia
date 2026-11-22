-- Prove2me | Theorems.Thm_Egrs75_RepairDV_highBlock_lowDigits
-- name    : Egrs75.RepairDV.highBlock_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:52.575853+00:00
-- url     : https://prove2.me/theorems/2c3a744c-4976-4a39-bfd8-6f070ea8d276
-- title:
--   Repair DV: high Block low Digits
-- statement:
--   **High block is `LowDigits q` (KERNEL-CLEAN).**  With `k = topBadIndex q n + 1`,
--   the high block `Hi = n / q^k` has no oversized base-`q` digit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L204-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L204-L217

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

theorem Egrs75.RepairDV.highBlock_lowDigits {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    LowDigits q (n / q ^ (topBadIndex q n + 1)) := by sorry
