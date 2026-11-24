-- Prove2me | Theorems.Thm_BondySimonovits_exists_large_cut
-- name    : BondySimonovits.exists_large_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:10.40831+00:00
-- url     : https://prove2.me/theorems/b02cd4bf-9f8f-44c2-85e6-3eaefad5bc60
-- title:
--   Bondy Simonovits: exists large cut
-- statement:
--   Max-cut: some 2-colouring cuts at least half of the edges (counted as ordered pairs).
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L206-L272
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L206-L272

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V]

theorem BondySimonovits.exists_large_cut (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : V → Bool, ∑ v, (univ.filter (G.Adj v)).card ≤
      2 * ∑ v, (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card := by sorry
