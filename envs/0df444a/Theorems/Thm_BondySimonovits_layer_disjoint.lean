-- Prove2me | Theorems.Thm_BondySimonovits_layer_disjoint
-- name    : BondySimonovits.layer_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.476794+00:00
-- url     : https://prove2.me/theorems/68e6b513-823b-4b57-ab85-ac5392c47efe
-- title:
--   Bondy Simonovits: layer disjoint
-- statement:
--   The Bondy Simonovits construction uses the layer disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L124-L128
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L124-L128

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]

theorem BondySimonovits.layer_disjoint (x : V) {i j : ℕ} (h : i ≠ j) : Disjoint (layer K x i) (layer K x j) := by sorry
