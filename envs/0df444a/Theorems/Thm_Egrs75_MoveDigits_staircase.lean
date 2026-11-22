-- Prove2me | Theorems.Thm_Egrs75_MoveDigits_staircase
-- name    : Egrs75.MoveDigits.staircase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:59.387437+00:00
-- url     : https://prove2.me/theorems/c095f510-ba0a-4048-b15f-b2bba84f7267
-- title:
--   Move Digits: staircase
-- statement:
--   **The staircase lemma (KERNEL-CLEAN).**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L174-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L174-L242

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

theorem Egrs75.MoveDigits.staircase {q : ℕ} (hq3 : 3 ≤ q) (hqo : Odd q) :
    ∀ i R : ℕ, 2 * R + 3 ≤ q ^ i →
      ∃ k, k < i ∧ R / q ^ k % q < (q - 1) / 2 ∧
        ∀ t, k < t → t < i → R / q ^ t % q = (q - 1) / 2 := by sorry
