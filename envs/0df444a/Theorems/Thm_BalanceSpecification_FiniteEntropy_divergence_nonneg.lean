-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_nonneg
-- name    : BalanceSpecification.FiniteEntropy.divergence_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:42.740452+00:00
-- url     : https://prove2.me/theorems/b0b9a645-7016-4862-b43f-172dd1f0984b
-- title:
--   Finite Entropy: divergence nonneg
-- statement:
--   Relative entropy of finite distributions is nonnegative whenever the
--   reference distribution supports the first one. No log of a zero denominator
--   is used for a nonzero summand.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L36-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L36-L41

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

theorem BalanceSpecification.FiniteEntropy.divergence_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hsupport : ∀ i, p i ≠ 0 → 0 < q i) : 0 ≤ divergence p q := by sorry
