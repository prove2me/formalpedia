-- Prove2me | Theorems.Thm_Egrs75_RepairDV_badCountQ_split
-- name    : Egrs75.RepairDV.badCountQ_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:12.731278+00:00
-- url     : https://prove2.me/theorems/6a95ff2f-1358-43c7-8fdd-33da801d50ec
-- title:
--   Repair DV: bad Count Q split
-- statement:
--   **Bad-count split (KERNEL-CLEAN).**  For `n = Lo + q^k · Hi` with `Lo < q^k`,
--   `Hi > 0`, `q ≥ 2`: the oversized-base-`q`-digit count is the sum of the low block's
--   and the high block's bad counts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean#L94-L97

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

theorem Egrs75.RepairDV.badCountQ_split {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    badCountQ q (Lo + q ^ k * Hi) = badCountQ q Lo + badCountQ q Hi := by sorry
