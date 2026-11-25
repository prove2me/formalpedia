-- Prove2me | Theorems.Thm_ErdosGirth_sum_wt
-- name    : ErdosGirth.sum_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:46.128281+00:00
-- url     : https://prove2.me/theorems/2f133d42-844d-5c1d-a533-37e280e26fd1
-- title:
--   Erdos Girth: sum wt
-- statement:
--   The Erdos Girth construction uses the sum wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L35-L38
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L35-L38

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.sum_wt (m : ℕ) (p : ℝ) : ∑ S ∈ (pairs m).powerset, wt m p S = 1 := by sorry
