-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_le_log_card
-- name    : BalanceSpecification.FiniteEntropy.shannon_le_log_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:24.311856+00:00
-- url     : https://prove2.me/theorems/cbc4f2e0-5e42-4b5a-bf16-ab92b4954b98
-- title:
--   Finite Entropy: shannon le log card
-- statement:
--   A finite probability distribution has entropy at most the log of the
--   number of possible outcomes.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L45-L66
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L45-L66

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

theorem BalanceSpecification.FiniteEntropy.shannon_le_log_card {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) : shannon p ≤ Real.log (Fintype.card ι) := by sorry
