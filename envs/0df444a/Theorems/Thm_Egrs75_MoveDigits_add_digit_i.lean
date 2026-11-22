-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_add_digit_i
-- name    : Egrs75.MoveDigits.add_digit_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:02.084644+00:00
-- url     : https://prove2.me/theorems/290849c2-4b77-45ec-9d3a-23308db837c8
-- title:
--   Move Digits: add digit i
-- statement:
--   **Digit at `i` becomes `b_i + 1`** under a single carry, when `b_i < q − 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L101-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L101-L108

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

theorem Egrs75.MoveDigits.add_digit_i {q : ℕ} (hq : 1 < q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) :
    (n + U) / q ^ i % q = n / q ^ i % q + 1 := by sorry
