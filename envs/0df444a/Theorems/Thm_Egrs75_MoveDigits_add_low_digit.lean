-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_add_low_digit
-- name    : Egrs75.MoveDigits.add_low_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:04.115393+00:00
-- url     : https://prove2.me/theorems/6c2effbf-69cb-493e-b87d-d015afece16c
-- title:
--   Move Digits: add low digit
-- statement:
--   **Digits below `i` of `n+U` are the digits of the new tail `R`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L125-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L125-L132

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem Egrs75.MoveDigits.add_low_digit {q : ℕ} (hq : 1 < q) (n U i t : ℕ) (ht : t < i)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    (n + U) / q ^ t % q = (n % q ^ i + U - q ^ i) / q ^ t % q := by sorry
