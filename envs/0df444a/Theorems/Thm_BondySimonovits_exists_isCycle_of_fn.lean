-- Prove2me | Theorems.Thm_BondySimonovits_exists_isCycle_of_fn
-- name    : BondySimonovits.exists_isCycle_of_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:04.221098+00:00
-- url     : https://prove2.me/theorems/5b8e1481-e388-42e1-8ead-5ce99f6efba3
-- title:
--   Bondy Simonovits: exists is Cycle of fn
-- statement:
--   The Bondy Simonovits construction uses the exists is Cycle of fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L42-L69
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L42-L69

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.exists_isCycle_of_fn (K : SimpleGraph V) (c : ℕ → V) (L : ℕ) (hL : 3 ≤ L)
    (hadj : ∀ t < L, K.Adj (c t) (c (t + 1))) (hclose : c L = c 0)
    (hinj : ∀ s < L, ∀ t < L, c s = c t → s = t) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = L := by sorry
