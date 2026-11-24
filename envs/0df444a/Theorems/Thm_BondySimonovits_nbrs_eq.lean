-- Prove2me | Theorems.Thm_BondySimonovits_nbrs_eq
-- name    : BondySimonovits.nbrs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:08:40.027831+00:00
-- url     : https://prove2.me/theorems/59452c3e-7fc5-4a34-8339-131f37c67165
-- title:
--   Bondy Simonovits: nbrs eq
-- statement:
--   The Bondy Simonovits construction uses the nbrs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L148-L160
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L148-L160

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf

theorem BondySimonovits.nbrs_eq (x : V) (i : ℕ) (u : V) (hu : u ∈ layer K x i) :
    univ.filter (K.Adj u) = (layer K x (i - 1) ∪ layer K x (i + 1)).filter (K.Adj u) := by sorry
