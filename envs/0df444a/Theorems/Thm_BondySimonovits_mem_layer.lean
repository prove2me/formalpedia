-- Prove2me | Theorems.Thm_BondySimonovits_mem_layer
-- name    : BondySimonovits.mem_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:05:17.670829+00:00
-- url     : https://prove2.me/theorems/547bac58-8d0b-4bc9-bea8-d7252df8fbbf
-- title:
--   Bondy Simonovits: mem layer
-- statement:
--   The Bondy Simonovits construction uses the mem layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L121-L122
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L121-L122

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]

theorem BondySimonovits.mem_layer {x v : V} {i : ℕ} : v ∈ layer K x i ↔ K.Reachable x v ∧ K.dist x v = i := by sorry
