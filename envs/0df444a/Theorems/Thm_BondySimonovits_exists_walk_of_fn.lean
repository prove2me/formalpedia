-- Prove2me | Theorems.Thm_BondySimonovits_exists_walk_of_fn
-- name    : BondySimonovits.exists_walk_of_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:02:55.458386+00:00
-- url     : https://prove2.me/theorems/f14c4c6d-a4a4-4a25-9a89-6c6e9ca1a29a
-- title:
--   Bondy Simonovits: exists walk of fn
-- statement:
--   The Bondy Simonovits construction uses the exists walk of fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L27-L40
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L27-L40

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.exists_walk_of_fn (K : SimpleGraph V) (c : ℕ → V) :
    ∀ n : ℕ, (∀ t < n, K.Adj (c t) (c (t + 1))) → ∀ u v, c 0 = u → c n = v →
      ∃ p : K.Walk u v, p.support = (List.range (n + 1)).map c ∧ p.length = n := by sorry
