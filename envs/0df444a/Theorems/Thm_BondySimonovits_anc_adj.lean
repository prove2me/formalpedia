-- Prove2me | Theorems.Thm_BondySimonovits_anc_adj
-- name    : BondySimonovits.anc_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:04:10.995801+00:00
-- url     : https://prove2.me/theorems/25359610-078f-41ec-98c3-3465fdd0d6c3
-- title:
--   Bondy Simonovits: anc adj
-- statement:
--   The Bondy Simonovits construction uses the anc adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L121-L130
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L121-L130

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

theorem BondySimonovits.anc_adj {t : ℕ} {v : V} (hr : K.Reachable x v) (ht : t < K.dist x v) :
    K.Adj (anc K par x (t + 1) v) (anc K par x t v) := by sorry
