-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_eq_neg_shannon_sub
-- name    : BalanceSpecification.FiniteEntropy.divergence_eq_neg_shannon_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:52.516934+00:00
-- url     : https://prove2.me/theorems/1bdb0535-c5cc-44d0-a7fa-8b9ba7650719
-- title:
--   Finite Entropy: divergence eq neg shannon sub
-- statement:
--   Finite relative entropy is negative Shannon entropy minus cross entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L36-L43
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L36-L43

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]

theorem BalanceSpecification.FiniteEntropy.divergence_eq_neg_shannon_sub {p q : ι → ℝ}
    (hq : ∀ i, 0 < q i) :
    divergence p q = -shannon p - ∑ i, p i * Real.log (q i) := by sorry
