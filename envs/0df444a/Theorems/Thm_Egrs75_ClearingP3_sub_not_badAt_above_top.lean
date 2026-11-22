-- Prove2me | Theorems.Thm_Egrs75_ClearingP3_sub_not_badAt_above_top
-- name    : Egrs75.ClearingP3.sub_not_badAt_above_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:49.31499+00:00
-- url     : https://prove2.me/theorems/f8d7cf70-07d1-440e-9ed3-a83ba6624ffe
-- title:
--   Clearing P3: sub not bad At above top
-- statement:
--   Above the top bad index (`idx > j`), the frozen digit of `n - S` is GOOD (it equals
--   the good digit of `n` there).  KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L372-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean#L372-L380

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

theorem Egrs75.ClearingP3.sub_not_badAt_above_top {q : ℕ} (hq : q.Prime) {n S : ℕ}
    (hbad : 0 < badCountQ q n) (hS : S ≤ n % q ^ (topBadIndex q n)) {idx : ℕ}
    (hidx : topBadIndex q n < idx) :
    ¬ BadAt q idx (n - S) := by sorry
