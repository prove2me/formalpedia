-- Prove2me | Theorems.Thm_BondySimonovits_anc_anc
-- name    : BondySimonovits.anc_anc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:45.254794+00:00
-- url     : https://prove2.me/theorems/a72c2447-007c-46ac-83e3-69ddbf66cc3c
-- title:
--   Bondy Simonovits: anc anc
-- statement:
--   The Bondy Simonovits construction uses the anc anc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L109-L115
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L109-L115

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

theorem BondySimonovits.anc_anc {r t : ℕ} {v : V} (hr : K.Reachable x v) (hrt : r ≤ t) (ht : t ≤ K.dist x v) :
    anc K par x r (anc K par x t v) = anc K par x r v := by sorry
