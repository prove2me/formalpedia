-- Prove2me | Theorems.Thm_Cage87_testBit_maskOf
-- name    : Cage87.testBit_maskOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:26:19.768179+00:00
-- url     : https://prove2.me/theorems/44edc901-1a5c-4345-a20e-8a54d1b875c7
-- title:
--   Cage87: test Bit mask Of
-- statement:
--   The Cage87 construction uses the test Bit mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L103-L116
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L103-L116

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

theorem Cage87.testBit_maskOf (z : Nat) : ∀ l : List Nat, (maskOf l).testBit z = true ↔ z ∈ l
  := by sorry
