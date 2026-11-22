-- Prove2me | Theorems.Thm_BinaryMatrix_card_toFinsetFamily_le
-- name    : BinaryMatrix.card_toFinsetFamily_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:45.002303+00:00
-- url     : https://prove2.me/theorems/b8add04b-6087-4fba-b5f8-fb57dd123f0d
-- title:
--   Binary Matrix: card to Finset Family le
-- statement:
--   **Sauer-Shelah lemma for binary matrices**: the number of distinct rows in the
--       Finset family is bounded by the sum of binomial coefficients up to the VC dimension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L101-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L101-L112

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix
set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix

theorem BinaryMatrix.card_toFinsetFamily_le {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.toFinsetFamily.vcDim ≤ d) :
    M.toFinsetFamily.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by sorry
