-- Prove2me | Theorems.Thm_BondySimonovits_degree_sum_layer
-- name    : BondySimonovits.degree_sum_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:08:42.403269+00:00
-- url     : https://prove2.me/theorems/75c91726-68c8-4eca-91b2-c08a83a98e1e
-- title:
--   Bondy Simonovits: degree sum layer
-- statement:
--   The Bondy Simonovits construction uses the degree sum layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L162-L167
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L162-L167

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

theorem BondySimonovits.degree_sum_layer (x : V) (i : ℕ) :
    ∑ u ∈ layer K x i, (univ.filter (K.Adj u)).card =
      ecount K (layer K x i) (layer K x (i - 1)) + ecount K (layer K x i) (layer K x (i + 1)) := by sorry
