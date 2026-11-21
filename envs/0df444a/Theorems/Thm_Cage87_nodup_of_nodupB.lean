-- Prove2me | Theorems.Thm_Cage87_nodup_of_nodupB
-- name    : Cage87.nodup_of_nodupB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:25:49.426636+00:00
-- url     : https://prove2.me/theorems/524d7bf5-9d7a-4225-b9c0-7192734d80b8
-- title:
--   Cage87: nodup of nodup B
-- statement:
--   The Cage87 construction uses the nodup of nodup B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L32-L39
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L32-L39

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

theorem Cage87.nodup_of_nodupB : ∀ l : List Nat, nodupB l = true → l.Nodup
  := by sorry
