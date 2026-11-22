-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_add_high_frozen
-- name    : Egrs75.MoveDigits.add_high_frozen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:01.733176+00:00
-- url     : https://prove2.me/theorems/39bb7d55-23b2-4d26-aa55-a97f3338653f
-- title:
--   Move Digits: add high frozen
-- statement:
--   **Digits above `i` are frozen** under a single carry, when `b_i < q − 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L111-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L111-L122

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

theorem Egrs75.MoveDigits.add_high_frozen {q : ℕ} (hq : 1 < q) (n U i idx : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) (hidx : i < idx) :
    (n + U) / q ^ idx % q = n / q ^ idx % q := by sorry
