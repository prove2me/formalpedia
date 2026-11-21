-- Prove2me | Theorems.Thm_Corless_isSign_star
-- name    : Corless.isSign_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:32.388199+00:00
-- url     : https://prove2.me/theorems/48852a26-619e-4a5c-9ab4-a5fb333e5a5c
-- title:
--   Corless: is Sign star
-- statement:
--   The Corless construction uses the is Sign star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L97-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean#L97-L98

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

theorem Corless.isSign_star (n m : ℕ) : IsSign (star n) m := by sorry
