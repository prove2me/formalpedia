-- Prove2me | Theorems.Thm_Cage87_girth_eq
-- name    : Cage87.girth_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:26:58.219473+00:00
-- url     : https://prove2.me/theorems/7fe0e4e3-7da2-4c73-a468-e686229613e0
-- title:
--   Cage87: girth eq
-- statement:
--   The Cage87 construction uses the girth eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L222-L226
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L222-L226

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

theorem Cage87.girth_eq : G.girth = 7 := by sorry
