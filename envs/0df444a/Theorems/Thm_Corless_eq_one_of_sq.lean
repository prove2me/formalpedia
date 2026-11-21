-- Prove2me | Theorems.Thm_Corless_eq_one_of_sq
-- name    : Corless.eq_one_of_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:08.199424+00:00
-- url     : https://prove2.me/theorems/41a87b0e-9524-48d5-91f3-af52a462f40f
-- title:
--   Corless: eq one of sq
-- statement:
--   The Corless construction uses the eq one of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L245-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L245-L250

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.eq_one_of_sq {p : ℤ[X]} (h : p ^ 2 = 1) (h0 : p.coeff 0 = 1) : p = 1 := by sorry
