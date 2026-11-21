-- Prove2me | Theorems.Thm_Corless_pow_two_of_frob
-- name    : Corless.pow_two_of_frob
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:33.969183+00:00
-- url     : https://prove2.me/theorems/cf5e64fc-dd54-4805-becd-b2cd4273c0cf
-- title:
--   Corless: pow two of frob
-- statement:
--   Over 𝔽₂, `(1 + X)^n = 1 + X^n` with `n ≥ 1` forces `n` to be a power of two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L153-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L153-L179

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.pow_two_of_frob : ∀ n : ℕ, 1 ≤ n → ((1 + X : (ZMod 2)[X]) ^ n = 1 + X ^ n) → ∃ a, n = 2 ^ a
  := by sorry
