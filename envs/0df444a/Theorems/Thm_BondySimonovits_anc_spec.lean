-- Prove2me | Theorems.Thm_BondySimonovits_anc_spec
-- name    : BondySimonovits.anc_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:33.59587+00:00
-- url     : https://prove2.me/theorems/595eb363-e2dd-442b-8b69-8d3814822a5b
-- title:
--   Bondy Simonovits: anc spec
-- statement:
--   The Bondy Simonovits construction uses the anc spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L104-L107
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L104-L107

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

theorem BondySimonovits.anc_spec {t : ℕ} {v : V} (hr : K.Reachable x v) (ht : t ≤ K.dist x v) :
    K.Reachable x (anc K par x t v) ∧ K.dist x (anc K par x t v) = t := by sorry
