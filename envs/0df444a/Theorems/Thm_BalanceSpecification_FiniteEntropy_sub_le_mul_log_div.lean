-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_sub_le_mul_log_div
-- name    : BalanceSpecification.FiniteEntropy.sub_le_mul_log_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:34.429298+00:00
-- url     : https://prove2.me/theorems/b3fb8895-ce98-4c96-b485-b5e7912259a6
-- title:
--   Finite Entropy: sub le mul log div
-- statement:
--   Gibbs' scalar log inequality, including a zero first weight.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L17-L31
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyAlgebra.lean#L17-L31

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

theorem BalanceSpecification.FiniteEntropy.sub_le_mul_log_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : p ≠ 0 → 0 < q) : p - q ≤ p * Real.log (p / q) := by sorry
