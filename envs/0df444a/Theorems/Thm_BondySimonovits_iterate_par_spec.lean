-- Prove2me | Theorems.Thm_BondySimonovits_iterate_par_spec
-- name    : BondySimonovits.iterate_par_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:29.795318+00:00
-- url     : https://prove2.me/theorems/d8b74051-c26f-46ac-a717-1601fa2ce58a
-- title:
--   Bondy Simonovits: iterate par spec
-- statement:
--   The Bondy Simonovits construction uses the iterate par spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L92-L102
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L92-L102

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

theorem BondySimonovits.iterate_par_spec : ∀ (n : ℕ) (v : V), K.Reachable x v → n ≤ K.dist x v →
    K.Reachable x (par^[n] v) ∧ K.dist x (par^[n] v) = K.dist x v - n := by sorry
