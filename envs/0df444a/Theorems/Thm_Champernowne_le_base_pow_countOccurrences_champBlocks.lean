-- Prove2me | Theorems.Thm_Champernowne_le_base_pow_countOccurrences_champBlocks
-- name    : Champernowne.le_base_pow_countOccurrences_champBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:16.400627+00:00
-- url     : https://prove2.me/theorems/0e5491af-766a-47d7-ae7f-f144af4fccad
-- title:
--   Champernowne: le base pow count Occurrences champ Blocks
-- statement:
--   General-`N` comparison, lower.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L503-L521
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L503-L521

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_base_pow_countOccurrences_champBlocks {b : ℕ} (hb : 1 < b) (N M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ N + 1) (h2 : N + 1 ≤ b ^ M) :
    (∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ M := by sorry
