-- Prove2me | Theorems.Thm_Corless_coeff_P_zero
-- name    : Corless.coeff_P_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:59.294848+00:00
-- url     : https://prove2.me/theorems/3697076a-f401-431e-ae6e-fc9893ef80c1
-- title:
--   Corless: coeff P zero
-- statement:
--   The Corless construction uses the coeff P zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L88-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L88-L93

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.coeff_P_zero (N j : ℕ) (hj : j < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff 0 = 1 := by sorry
