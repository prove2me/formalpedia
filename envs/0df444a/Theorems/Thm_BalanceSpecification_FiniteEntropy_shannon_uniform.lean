-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_uniform
-- name    : BalanceSpecification.FiniteEntropy.shannon_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:28.905293+00:00
-- url     : https://prove2.me/theorems/474b383e-4a43-48f1-b390-667e87c1955d
-- title:
--   Finite Entropy: shannon uniform
-- statement:
--   Uniform probability on a nonempty finite type has entropy the logarithm
--   of its cardinality.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L69-L75
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L69-L75

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

theorem BalanceSpecification.FiniteEntropy.shannon_uniform [Nonempty ι] :
    shannon (fun _ : ι => 1 / (Fintype.card ι : ℝ)) = Real.log (Fintype.card ι) := by sorry
