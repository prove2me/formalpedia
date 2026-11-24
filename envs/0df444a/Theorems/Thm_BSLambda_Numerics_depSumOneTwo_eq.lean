-- Prove2me | Theorems.Thm_BSLambda_Numerics_depSumOneTwo_eq
-- name    : BSLambda.Numerics.depSumOneTwo_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:18.093583+00:00
-- url     : https://prove2.me/theorems/edcfbf7f-1c70-4362-81cf-0d5f52f11ef7
-- title:
--   Numerics: dep Sum One Two eq
-- statement:
--   The number of type-2 events meeting a fixed five-element support in at least two
--   vertices, `D_12 = ∑_{s=2}^{5} C(5,s) C(14006,9-s) = 209,572,451,535,510,643,927,671,555`
--   (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L68-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L68-L71

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

theorem BSLambda.Numerics.depSumOneTwo_eq :
    ∑ s ∈ Finset.Icc 2 5, Nat.choose 5 s * Nat.choose 14006 (9 - s) =
      209572451535510643927671555 := by sorry
