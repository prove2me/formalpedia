-- Prove2me | Theorems.Thm_BondySimonovits_layer_claim
-- name    : BondySimonovits.layer_claim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:09:32.556886+00:00
-- url     : https://prove2.me/theorems/6a828125-97b8-44f5-83b2-0ae6efed2143
-- title:
--   Bondy Simonovits: layer claim
-- statement:
--   Two consecutive layers below level `k` span few edges, otherwise the key lemma produces a
--   cycle of length `2k`.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L171-L196
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L171-L196

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf

theorem BondySimonovits.layer_claim (x : V) (k : ℕ) (hk : 2 ≤ k)
    (hcyc : ∀ (v : V) (p : K.Walk v v), p.IsCycle → p.length ≠ 2 * k) (i : ℕ) (hik : i + 1 ≤ k) :
    ecount K (layer K x i) (layer K x (i + 1)) ≤
      2 * k * ((layer K x i).card + (layer K x (i + 1)).card) := by sorry
