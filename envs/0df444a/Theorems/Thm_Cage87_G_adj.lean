-- Prove2me | Theorems.Thm_Cage87_G_adj
-- name    : Cage87.G_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:25:48.596748+00:00
-- url     : https://prove2.me/theorems/33ff1ddf-a674-4656-9add-b240c4c964db
-- title:
--   Cage87: G adj
-- statement:
--   The Cage87 construction uses the G adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L84-L84
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L84-L84

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

theorem Cage87.G_adj (u v : Fin 768) : G.Adj u v ↔ v.val ∈ nb adj u.val := by sorry
