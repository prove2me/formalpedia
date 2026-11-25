-- Prove2me | Theorems.Thm_Expanders_vertexBall_step
-- name    : Expanders.vertexBall_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:16.002575+00:00
-- url     : https://prove2.me/theorems/a6f3dc2f-6699-5222-95ef-6dd5482c4031
-- title:
--   Expanders: vertex Ball step
-- statement:
--   The Expanders construction uses the vertex Ball step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L381-L385
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L381-L385

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}

theorem Expanders.vertexBall_step : ∀ v ∈ vertexBall G u k, ∀ w ∈ vertexBall G u k, G.Adj v w →
    G.dist u w - 1 ≤ G.dist u v - 1 + 1 := by sorry
