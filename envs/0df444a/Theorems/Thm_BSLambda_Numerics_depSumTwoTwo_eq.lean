-- Prove2me | Theorems.Thm_BSLambda_Numerics_depSumTwoTwo_eq
-- name    : BSLambda.Numerics.depSumTwoTwo_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:18.685513+00:00
-- url     : https://prove2.me/theorems/270f6d46-f994-4266-a27f-c382158c8e07
-- title:
--   Numerics: dep Sum Two Two eq
-- statement:
--   The number of other nine-element supports meeting a fixed nine-element support in at
--   least two vertices, `D_22 = (∑_{s=2}^{9} C(9,s) C(14002,9-s)) - 1`
--   `= 753,455,972,623,601,870,517,771,054` (Section 10.1); the subtraction removes the event
--   itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L77-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L77-L80

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

theorem BSLambda.Numerics.depSumTwoTwo_eq :
    (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 =
      753455972623601870517771054 := by sorry
