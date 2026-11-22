-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_add_div_pow_eq
-- name    : Egrs75.MoveDigits.add_div_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:30.430558+00:00
-- url     : https://prove2.me/theorems/aa67e25b-a9db-4a32-98e1-d5016eb133f2
-- title:
--   Move Digits: add div pow eq
-- statement:
--   Under a single carry (`q^i ≤ T+U < 2q^i`), the block above `i` increments:
--   `(n+U)/q^i = n/q^i + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L78-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L78-L84

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

theorem Egrs75.MoveDigits.add_div_pow_eq {q : ℕ} (hq : 1 < q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i) :
    (n + U) / q ^ i = n / q ^ i + 1 := by sorry
