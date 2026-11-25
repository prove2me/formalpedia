-- Prove2me | Theorems.Thm_Expanders_mem_vertexBall
-- name    : Expanders.mem_vertexBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:08:25.992741+00:00
-- url     : https://prove2.me/theorems/57a7442c-e4bd-5240-ae16-b3947dd20121
-- title:
--   Expanders: mem vertex Ball
-- statement:
--   The Expanders construction uses the mem vertex Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L360-L362
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L360-L362

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.mem_vertexBall {G : SimpleGraph V} {u v : V} {k : ℕ} :
    v ∈ vertexBall G u k ↔ G.Reachable u v ∧ G.dist u v ≤ k + 1 := by sorry
