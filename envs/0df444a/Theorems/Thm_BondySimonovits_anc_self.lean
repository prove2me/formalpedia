-- Prove2me | Theorems.Thm_BondySimonovits_anc_self
-- name    : BondySimonovits.anc_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:41.958468+00:00
-- url     : https://prove2.me/theorems/43b53830-56c3-4c3e-b48a-8487d00ac1f6
-- title:
--   Bondy Simonovits: anc self
-- statement:
--   The Bondy Simonovits construction uses the anc self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L118-L119
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L118-L119

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
omit hpar

theorem BondySimonovits.anc_self (v : V) : anc K par x (K.dist x v) v = v := by sorry
