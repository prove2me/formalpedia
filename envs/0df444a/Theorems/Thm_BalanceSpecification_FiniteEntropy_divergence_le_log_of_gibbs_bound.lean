-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_le_log_of_gibbs_bound
-- name    : BalanceSpecification.FiniteEntropy.divergence_le_log_of_gibbs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:12.508266+00:00
-- url     : https://prove2.me/theorems/83e7c076-5d4a-4141-ac69-9466e6d24af3
-- title:
--   Finite Entropy: divergence le log of gibbs bound
-- statement:
--   The finite Gibbs estimate used in the intrinsic-ergodicity proof.
--   All hypotheses here are explicit numerical inputs; passing from these finite
--   bounds to relative entropy of measures is a separate theorem.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L48-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L48-L65

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

theorem BalanceSpecification.FiniteEntropy.divergence_le_log_of_gibbs_bound {p q : ι → ℝ} {K t : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hK : 0 < K)
    (hq : ∀ i, Real.exp (-t) / K ≤ q i) (hentropy : t ≤ shannon p) :
    divergence p q ≤ Real.log K := by sorry
