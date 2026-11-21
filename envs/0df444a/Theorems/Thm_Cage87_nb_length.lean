-- Prove2me | Theorems.Thm_Cage87_nb_length
-- name    : Cage87.nb_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:25:51.202382+00:00
-- url     : https://prove2.me/theorems/6aca4f5f-dce9-4f7a-bb9f-ccc14a8ed798
-- title:
--   Cage87: nb length
-- statement:
--   The Cage87 construction uses the nb length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L54-L57
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L54-L57

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

theorem Cage87.nb_length : (nb adj v).length = 8 := by sorry
