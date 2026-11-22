-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_quadratic_step_le_exp2
-- name    : DeciSigma1.Arithmetic.quadratic_step_le_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:15.727799+00:00
-- url     : https://prove2.me/theorems/8004047e-2b5f-4d71-8ad9-662275509e82
-- title:
--   Arithmetic: quadratic step le exp2
-- statement:
--   A quadratic step with exponentially bounded coefficients has a linear exponent bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L132-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L132-L151

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic

theorem DeciSigma1.Arithmetic.quadratic_step_le_exp2 {t a e q L : ℕ}
    (ht : t ≤ exp2 L) (ha : a ≤ exp2 q) (he : e ≤ exp2 q) :
    t + (t * a) * ((t * a + 2) * e) ≤ exp2 (2 * L + 3 * q + 3) := by sorry
