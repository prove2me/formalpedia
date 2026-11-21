-- Prove2me | Theorems.Thm_Cage87_nb_nodup
-- name    : Cage87.nb_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:26:09.350613+00:00
-- url     : https://prove2.me/theorems/bb6c3d3a-65eb-4959-b6c0-e65fbef7edbc
-- title:
--   Cage87: nb nodup
-- statement:
--   The Cage87 construction uses the nb nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L59-L62
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L59-L62

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
variable {v : Nat} (hv : v < 768)
include hv

theorem Cage87.nb_nodup : (nb adj v).Nodup := by sorry
