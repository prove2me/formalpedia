-- Prove2me | Theorems.Thm_Cage87_isRegular
-- name    : Cage87.isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:26:13.745298+00:00
-- url     : https://prove2.me/theorems/be707e78-c5f3-4883-b21c-17d323db493a
-- title:
--   Cage87: is Regular
-- statement:
--   The Cage87 construction uses the is Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L99-L99
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L99-L99

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

theorem Cage87.isRegular : G.IsRegularOfDegree 8 := by sorry
