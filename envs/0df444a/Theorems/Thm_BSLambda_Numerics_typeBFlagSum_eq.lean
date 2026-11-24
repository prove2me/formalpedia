-- Prove2me | Theorems.Thm_BSLambda_Numerics_typeBFlagSum_eq
-- name    : BSLambda.Numerics.typeBFlagSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:24:31.839895+00:00
-- url     : https://prove2.me/theorems/7f5279fd-9460-4a4b-bc10-203f2e753775
-- title:
--   Numerics: type BFlag Sum eq
-- statement:
--   The number of Type-B radius-one flags through a fixed pair,
--   `N_B = C(t,3) + 2 t C(t-1,2) + C(t,2) (t-2) = 71,519,595,000` at `t = 3502` (Section 8.2).
--   Together with `typeAFlagSum_eq` this gives `N_1 = N_A + N_B = 214,620,087,510`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L52-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean#L52-L55

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial

theorem BSLambda.Numerics.typeBFlagSum_eq :
    Nat.choose 3502 3 + 2 * 3502 * Nat.choose 3501 2 + Nat.choose 3502 2 * 3500 =
      71519595000 := by sorry
