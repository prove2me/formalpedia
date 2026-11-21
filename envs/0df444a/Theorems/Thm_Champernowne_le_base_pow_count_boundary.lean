-- Prove2me | Theorems.Thm_Champernowne_le_base_pow_count_boundary
-- name    : Champernowne.le_base_pow_count_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:16.001632+00:00
-- url     : https://prove2.me/theorems/c6a4c3df-1b7c-4ae2-9fe8-c7e3b4be8871
-- title:
--   Champernowne: le base pow count boundary
-- statement:
--   Boundary comparison, lower: over the complete cohorts `[1, b^K)`, the
--   stream length exceeds `b^k` times the occurrence count by at most
--   `6·(k+1)·b^K`. Each full cohort `[b^K, b^(K+1))` is a partial cohort with
--   `t = b^(K+1) - b^K` (`le_base_pow_countOccurrences_partial`); the
--   geometric accumulation of the per-cohort errors `3(k+1)·b^(K+1)` stays
--   below `6(k+1)·b^K` because `2 ≤ b`. Cohorts too short to fit `w` only
--   need their length bounded (the occurrence count is dropped at `≥ 0`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L465-L500
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L465-L500

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_base_pow_count_boundary {b : ℕ} (hb : 1 < b) (K : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (∑ n ∈ Finset.Ico 1 (b ^ K), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico 1 (b ^ K), countOccurrences w (bigDigits b n))
        + 6 * (w.length + 1) * b ^ K := by sorry
