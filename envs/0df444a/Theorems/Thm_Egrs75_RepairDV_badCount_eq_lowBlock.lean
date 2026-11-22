-- Prove2me | Theorems.Thm_Egrs75_RepairDV_badCount_eq_lowBlock
-- name    : Egrs75.RepairDV.badCount_eq_lowBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:04.081529+00:00
-- url     : https://prove2.me/theorems/e335b3ff-fd1e-43c8-9cce-5f606c92a4db
-- title:
--   Repair DV: bad Count eq low Block
-- statement:
--   **Decomposition (KERNEL-CLEAN).**  With `k = topBadIndex q n + 1`, the bad count of
--   `n` equals the bad count of its low block `n % q^k`, and that is `≥ 1`.  Moreover the
--   high block `n / q^k` is positive (the top bad digit forces `n ≥ q^(k-1) > 0`, and
--   since the digit at `topBadIndex` is nonzero the number extends at least that far).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L240-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L240-L263

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

theorem Egrs75.RepairDV.badCount_eq_lowBlock {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    badCountQ q n = badCountQ q (n % q ^ (topBadIndex q n + 1)) := by sorry
