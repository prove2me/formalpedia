-- Prove2me | Theorems.Thm_BondySimonovits_layer_growth
-- name    : BondySimonovits.layer_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:07:32.185227+00:00
-- url     : https://prove2.me/theorems/c19ab73d-bbbf-43e8-a72e-5bee7866f1e7
-- title:
--   Bondy Simonovits: layer growth
-- statement:
--   The pure recursion: from `d a_i ≤ D (a_{i-1} + a_i) + D (a_i + a_{i+1})` we get geometric
--   growth with ratio `d / D - 3`.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L69-L109
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L69-L109

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits

theorem BondySimonovits.layer_growth (a : ℕ → ℕ) (k d D : ℕ) (hD : 0 < D) (hdD : 4 * D ≤ d) (h0 : a 0 ≤ 1)
    (h1 : d ≤ a 1)
    (hrec : ∀ i, 1 ≤ i → i + 1 ≤ k → d * a i ≤ D * (a (i - 1) + a i) + D * (a i + a (i + 1))) :
    ∀ i, 1 ≤ i → i ≤ k → ((d : ℝ) / D - 3) ^ i ≤ a i ∧ a (i - 1) ≤ a i := by sorry
