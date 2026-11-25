-- Prove2me | Theorems.Thm_ErdosGirth_bound_indep
-- name    : ErdosGirth.bound_indep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:28:49.805928+00:00
-- url     : https://prove2.me/theorems/dd045522-f9ee-5a08-bfba-91c04eaa39a8
-- title:
--   Erdos Girth: bound indep
-- statement:
--   The Erdos Girth construction uses the bound indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L438-L469
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L438-L469

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.bound_indep (a q t : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q)
    (ht : t = q ^ (a + 1)) (m : ℝ) (hm0 : 0 ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (a + 2)) :
    m ^ t * (1 - 1 / (q : ℝ) ^ a) ^ t.choose 2 ≤ 1 / 2 := by sorry
