-- Prove2me | Theorems.Thm_Corless_Dv_star
-- name    : Corless.Dv_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:39.355337+00:00
-- url     : https://prove2.me/theorems/6ceba0b9-ceaa-46b1-87ae-35268abba87e
-- title:
--   Corless: Dv star
-- statement:
--   The Corless construction uses the Dv star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L100-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L100-L112

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

theorem Corless.Dv_star (n : ℕ) : Dv (star n) (2 * n + 3) = f (n + 1) ^ 2 := by sorry
