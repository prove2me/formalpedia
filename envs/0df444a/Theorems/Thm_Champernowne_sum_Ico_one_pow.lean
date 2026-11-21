-- Prove2me | Theorems.Thm_Champernowne_sum_Ico_one_pow
-- name    : Champernowne.sum_Ico_one_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:47.058284+00:00
-- url     : https://prove2.me/theorems/d2a59c53-213b-4ed0-96d2-ade04aa356ef
-- title:
--   Champernowne: sum Ico one pow
-- statement:
--   Cohort decomposition of a sum over `[1, b^M)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L155-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L155-L165

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_Ico_one_pow {β : Type*} [AddCommMonoid β] {b : ℕ} (hb : 1 < b)
    (M : ℕ) (g : ℕ → β) :
    ∑ n ∈ Finset.Ico 1 (b ^ M), g n
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), g n := by sorry
