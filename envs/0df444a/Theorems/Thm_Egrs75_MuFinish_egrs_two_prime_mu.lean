-- Prove2me | Theorems.Thm_Egrs75_MuFinish_egrs_two_prime_mu
-- name    : Egrs75.MuFinish.egrs_two_prime_mu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:58.879022+00:00
-- url     : https://prove2.me/theorems/c2935a77-9e63-432c-8e96-a84156d0358b
-- title:
--   Mu Finish: egrs two prime mu
-- statement:
--   **EGRS75 two-prime theorem — CLOSED (KERNEL-CLEAN, no sorry).**  For
--   distinct odd primes `p q`, there are infinitely many `n` with `p ∤ C(2n,n)` and
--   `q ∤ C(2n,n)`.  (Erdős–Graham–Ruzsa–Straus, Math. Comp. 29 (1975), Theorem 1,
--   equality case — a KNOWN theorem; this is its machine-checked proof.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L445-L449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L445-L449

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_MuFinish
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4

theorem Egrs75.MuFinish.egrs_two_prime_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by sorry
