-- Prove2me | Theorems.Thm_BondySimonovits_parent_exists
-- name    : BondySimonovits.parent_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:35.766225+00:00
-- url     : https://prove2.me/theorems/299493ab-7846-4e40-b754-2304f013c27e
-- title:
--   Bondy Simonovits: parent exists
-- statement:
--   The Bondy Simonovits construction uses the parent exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L66-L82
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L66-L82

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)

theorem BondySimonovits.parent_exists {x v : V} (hr : K.Reachable x v) (hpos : 0 < K.dist x v) :
    ∃ w, K.Adj v w ∧ K.dist x w + 1 = K.dist x v := by sorry
