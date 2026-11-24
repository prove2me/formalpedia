-- Prove2me | Theorems.Thm_BondySimonovits_dist_ne_of_adj
-- name    : BondySimonovits.dist_ne_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:32.094835+00:00
-- url     : https://prove2.me/theorems/9d3d960f-0988-410d-86ee-38685c1e1497
-- title:
--   Bondy Simonovits: dist ne of adj
-- statement:
--   The Bondy Simonovits construction uses the dist ne of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L44-L55
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean#L44-L55

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)

theorem BondySimonovits.dist_ne_of_adj (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) {x u v : V}
    (hr : K.Reachable x u) (h : K.Adj u v) : K.dist x u ≠ K.dist x v := by sorry
