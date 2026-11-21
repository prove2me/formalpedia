-- Prove2me | Theorems.Thm_Cage87_pairwise_rel
-- name    : Cage87.pairwise_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:26:30.733178+00:00
-- url     : https://prove2.me/theorems/8c32d4e4-808c-40c3-bd96-9913ae25b837
-- title:
--   Cage87: pairwise rel
-- statement:
--   The Cage87 construction uses the pairwise rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L124-L133
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean#L124-L133

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

theorem Cage87.pairwise_rel {α : Type*} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  := by sorry
