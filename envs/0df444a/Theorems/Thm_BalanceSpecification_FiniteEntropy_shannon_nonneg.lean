-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_nonneg
-- name    : BalanceSpecification.FiniteEntropy.shannon_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:25.755513+00:00
-- url     : https://prove2.me/theorems/5289cba4-6a46-427b-9080-a72b9c0a874e
-- title:
--   Finite Entropy: shannon nonneg
-- statement:
--   Shannon entropy is nonnegative for a probability distribution.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L69-L77
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L69-L77

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]

theorem BalanceSpecification.FiniteEntropy.shannon_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : 0 ≤ shannon p := by sorry
