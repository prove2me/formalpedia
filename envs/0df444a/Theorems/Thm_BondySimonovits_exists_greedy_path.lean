-- Prove2me | Theorems.Thm_BondySimonovits_exists_greedy_path
-- name    : BondySimonovits.exists_greedy_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:00.460962+00:00
-- url     : https://prove2.me/theorems/cc510cd7-5778-483b-bbeb-124e25039b12
-- title:
--   Bondy Simonovits: exists greedy path
-- statement:
--   Greedy path in a subset of large minimum degree, avoiding a small forbidden set.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L151-L197
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L151-L197

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.exists_greedy_path (K : SimpleGraph V) [DecidableRel K.Adj] (Y Z : Finset V) (D : ℕ)
    (hY : ∀ v ∈ Y, D ≤ (Y.filter (K.Adj v)).card) (w : V) (hw : w ∈ Y) (hwZ : w ∉ Z) :
    ∀ m, m + Z.card < D → ∃ q : ℕ → V, q 0 = w ∧ (∀ t < m, K.Adj (q t) (q (t + 1))) ∧
      (∀ t ≤ m, q t ∈ Y ∧ q t ∉ Z) ∧ (∀ s ≤ m, ∀ t ≤ m, q s = q t → s = t) := by sorry
