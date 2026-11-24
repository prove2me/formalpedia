-- Prove2me | Theorems.Thm_BondySimonovits_adj_levels
-- name    : BondySimonovits.adj_levels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:38.12894+00:00
-- url     : https://prove2.me/theorems/50433bb6-f0b3-4a08-92c7-0cca9c376c2c
-- title:
--   Bondy Simonovits: adj levels
-- statement:
--   The Bondy Simonovits construction uses the adj levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L57-L64
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L57-L64

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)

theorem BondySimonovits.adj_levels (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) {x u v : V}
    (hr : K.Reachable x u) (h : K.Adj u v) :
    K.Reachable x v ∧ (K.dist x v = K.dist x u + 1 ∨ K.dist x u = K.dist x v + 1) := by sorry
