-- Prove2me | Theorems.Thm_BSLambda_Numerics_typeAFlagSum_eq
-- name    : BSLambda.Numerics.typeAFlagSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:15.565794+00:00
-- url     : https://prove2.me/theorems/cc507c21-4c29-4d0a-8d62-128ec230a567
-- title:
--   Numerics: type AFlag Sum eq
-- statement:
--   The number of Type-A radius-one flags through a fixed pair,
--   `N_A = C(d-1,3) + t * C(d-2,2) = 143,100,492,510` at `d = 7005`, `t = 3502` (Section 8.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L47-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L47-L47

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

theorem BSLambda.Numerics.typeAFlagSum_eq : Nat.choose 7004 3 + 3502 * Nat.choose 7003 2 = 143100492510 := by sorry
