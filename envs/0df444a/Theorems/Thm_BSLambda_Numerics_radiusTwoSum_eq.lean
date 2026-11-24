-- Prove2me | Theorems.Thm_BSLambda_Numerics_radiusTwoSum_eq
-- name    : BSLambda.Numerics.radiusTwoSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:25.194619+00:00
-- url     : https://prove2.me/theorems/26bac598-c564-48eb-af92-b011957e65be
-- title:
--   Numerics: radius Two Sum eq
-- statement:
--   The radius-two obstruction constant
--   `K = 9 * 2^20 * ∑_{l=0}^{8} C(8,l) C(28,8-l) 2^l = 1,300,311,466,573,824` (Section 9); the
--   Lean declaration for this number is `BSLambda.LLL.radiusTwoConst`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L60-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L60-L63

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

theorem BSLambda.Numerics.radiusTwoSum_eq :
    9 * 2 ^ 20 * (∑ l ∈ Finset.range 9, Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l) =
      1300311466573824 := by sorry
