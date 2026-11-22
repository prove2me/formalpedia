-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_add_carry_decomp
-- name    : Egrs75.MoveDigits.add_carry_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:42.192851+00:00
-- url     : https://prove2.me/theorems/2b6547cd-12be-4a90-b6b1-405d48b99ffc
-- title:
--   Move Digits: add carry decomp
-- statement:
--   The carry decomposition `n + U = R + q^i·(H+1)`, `R = (T+U) − q^i`,
--   `H = n / q^i`, valid when `q^i ≤ T + U` with `T = n % q^i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L68-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L68-L74

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

theorem Egrs75.MoveDigits.add_carry_decomp {q : ℕ} (hq : 1 ≤ q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    n + U = (n % q ^ i + U - q ^ i) + q ^ i * (n / q ^ i + 1) := by sorry
