-- Prove2me | Theorems.Thm_ErdosGirth_two_mul_pow_le_exp
-- name    : ErdosGirth.two_mul_pow_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:01.014078+00:00
-- url     : https://prove2.me/theorems/8667e03c-8528-4737-bd59-d55c5522a18e
-- title:
--   Erdos Girth: two mul pow le exp
-- statement:
--   The Erdos Girth construction uses the two mul pow le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L409-L436
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L409-L436

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.two_mul_pow_le_exp (a q : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q) :
    2 * ((q : ℝ) + 1) ^ (a + 2) ≤ Real.exp (((q : ℝ) - 1) / 2) := by sorry
