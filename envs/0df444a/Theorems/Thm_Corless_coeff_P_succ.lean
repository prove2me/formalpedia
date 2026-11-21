-- Prove2me | Theorems.Thm_Corless_coeff_P_succ
-- name    : Corless.coeff_P_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:00.762394+00:00
-- url     : https://prove2.me/theorems/0df27f0b-4b92-4086-bae8-bd64c018cb12
-- title:
--   Corless: coeff P succ
-- statement:
--   The Corless construction uses the coeff P succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L95-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L95-L114

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.coeff_P_succ (N j i : ℕ) (hj : j < N) (hi : i < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff (i + 1)
      = ((2 * N + 1).choose (i + 1) : ZMod 2)
        + if j ≤ i then ((2 * N - j).choose (i - j) : ZMod 2) else 0 := by sorry
