-- Prove2me | Theorems.Thm_Egrs75_MuFinish_egrs_move
-- name    : Egrs75.MuFinish.egrs_move
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:16.202025+00:00
-- url     : https://prove2.me/theorems/ac6e994c-ab55-4246-b515-e6cee9d5d453
-- title:
--   Mu Finish: egrs move
-- statement:
--   **THE EGRS75 SINGLE MOVE (KERNEL-CLEAN, no sorry).**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L136-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L136-L276

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

theorem Egrs75.MuFinish.egrs_move {p q : ℕ} (hp : p.Prime) (_hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (_hpq : p ≠ q) (hq3 : 3 ≤ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hbad : 0 < badCountQ q n)
    (hfloor : N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n', LowDigits p n' ∧
      N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
      (muVal q hq3 n' < muVal q hq3 n ∨
        (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)) := by sorry
