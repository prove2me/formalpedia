-- Prove2me | Theorems.Thm_BooleanIsoperimetry_int_sum_mul_le_of_prefix_le_of_antitone_weight
-- name    : BooleanIsoperimetry.int_sum_mul_le_of_prefix_le_of_antitone_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:03.064447+00:00
-- url     : https://prove2.me/theorems/11d269d0-4494-42f2-bdba-eca4f979d46b
-- title:
--   Boolean Isoperimetry: int sum mul le of prefix le of antitone weight
-- statement:
--   Abel summation majorization over ℤ: if `v` is majorized by `u` in prefix sums,
--   and `w` is antitone, then the `w`-weighted sum of `v` is ≤ that of `u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L62-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L62-L102

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.int_sum_mul_le_of_prefix_le_of_antitone_weight
    (M : ℕ) (u v w : ℕ → ℤ)
    (hpref : ∀ r ≤ M, ∑ i ∈ Finset.range r, v i ≤ ∑ i ∈ Finset.range r, u i)
    (htot : ∑ i ∈ Finset.range M, u i = ∑ i ∈ Finset.range M, v i)
    (_ : ∀ i, i < M → 0 ≤ w i)
    (hwanti : ∀ i, i + 1 < M → w (i + 1) ≤ w i) :
    ∑ i ∈ Finset.range M, w i * v i ≤ ∑ i ∈ Finset.range M, w i * u i := by sorry
