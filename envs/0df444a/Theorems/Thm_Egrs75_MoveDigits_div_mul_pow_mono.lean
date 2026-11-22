-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_div_mul_pow_mono
-- name    : Egrs75.MoveDigits.div_mul_pow_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:44.516419+00:00
-- url     : https://prove2.me/theorems/7fb28743-652a-4e14-902c-29b64901b565
-- title:
--   Move Digits: div mul pow mono
-- statement:
--   Keeping MORE high digits keeps a larger (or equal) value:
--   `n/q^b · q^b ≤ n/q^a · q^a` for `a ≤ b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L53-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L53-L62

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

theorem Egrs75.MoveDigits.div_mul_pow_mono {q : ℕ} (_hq : 0 < q) (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    n / q ^ b * q ^ b ≤ n / q ^ a * q ^ a := by sorry
