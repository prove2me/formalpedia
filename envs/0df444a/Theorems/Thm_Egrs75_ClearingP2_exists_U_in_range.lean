-- Prove2me | Theorems.Thm_Egrs75_ClearingP2_exists_U_in_range
-- name    : Egrs75.ClearingP2.exists_U_in_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:16.750523+00:00
-- url     : https://prove2.me/theorems/cb6e379e-105b-44e9-8ab6-7f7b60a08b42
-- title:
--   Clearing P2: exists U in range
-- statement:
--   **The ADD-branch correction exists (KERNEL-CLEAN).**  For odd `p ≥ 3`, set
--   `x = q^i - T`.  If `1 ≤ x` (a genuine clearing window) and `2*x ≤ p^m` (the equality
--   -case form of EGRS condition (3): `q^i - 1 < ((q-1)/B)((p-A-1)/(p-1))(p^m-1)` collapses
--   to `2(q^i - T) ≤ p^m` at `A = B = (p-1)/2 = (q-1)/2`), then there is a `LowDigits p`
--   number `U` with `q^i - T ≤ U` and `U < p^m`.
--
--   Drawn from the density Fact `RoundUp.exists_lowDigits_between` (interval `[x, 2x)`,
--   ratio `(p-1)/A = 2`); `U < 2x ≤ p^m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L138-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/AddBranch.lean#L138-L142

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.ClearingP2.exists_U_in_range {p q i T m : ℕ} (hp : 3 ≤ p) (hpo : Odd p)
    (hx1 : 1 ≤ q ^ i - T) (hcond3 : 2 * (q ^ i - T) ≤ p ^ m) :
    ∃ U, q ^ i - T ≤ U ∧ U < p ^ m ∧ LowDigits p U := by sorry
