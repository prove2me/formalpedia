-- Prove2me | Theorems.Thm_BondySimonovits_anc_zero
-- name    : BondySimonovits.anc_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:04:06.332323+00:00
-- url     : https://prove2.me/theorems/21f89694-63fe-4ca4-98af-34c6f9fc4768
-- title:
--   Bondy Simonovits: anc zero
-- statement:
--   The Bondy Simonovits construction uses the anc zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L132-L134
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L132-L134

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
variable {K} {par : V → V} {x : V}
  (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
    K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
include hpar

theorem BondySimonovits.anc_zero {v : V} (hr : K.Reachable x v) : anc K par x 0 v = x := by sorry
