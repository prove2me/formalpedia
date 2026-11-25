-- Prove2me | Theorems.Thm_ErdosGirth_sum_wt_cycle
-- name    : ErdosGirth.sum_wt_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:11.811803+00:00
-- url     : https://prove2.me/theorems/29779192-5807-4ab4-8624-f33ecd0d59bd
-- title:
--   Erdos Girth: sum wt cycle
-- statement:
--   The Erdos Girth construction uses the sum wt cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L132-L139
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L132-L139

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical

theorem ErdosGirth.sum_wt_cycle {m : ℕ} (p : ℝ) {u : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u u) :
    ∑ S ∈ (pairs m).powerset, wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0)
      = if c.IsCycle then p ^ c.length else 0 := by sorry
