-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_joint_le
-- name    : BalanceSpecification.FiniteEntropy.shannon_joint_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:41.931838+00:00
-- url     : https://prove2.me/theorems/154e5cb4-49e7-4fd5-a8ff-e54e464e15a7
-- title:
--   Finite Entropy: shannon joint le
-- statement:
--   Shannon entropy of a joint finite distribution is bounded by the sum
--   of the entropies of its two marginals.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L81-L129
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L81-L129

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

theorem BalanceSpecification.FiniteEntropy.shannon_joint_le {κ : Type*} [Fintype κ] {p : ι × κ → ℝ}
    (hp : ∀ ij, 0 ≤ p ij) (hsum : ∑ ij, p ij = 1) :
    shannon p ≤ shannon (fun i => ∑ j, p (i, j)) +
      shannon (fun j => ∑ i, p (i, j)) := by sorry
