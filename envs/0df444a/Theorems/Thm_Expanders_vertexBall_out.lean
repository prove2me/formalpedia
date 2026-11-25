-- Prove2me | Theorems.Thm_Expanders_vertexBall_out
-- name    : Expanders.vertexBall_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:11.080696+00:00
-- url     : https://prove2.me/theorems/df41d71b-7a49-4f7a-a114-32208c5c16de
-- title:
--   Expanders: vertex Ball out
-- statement:
--   The Expanders construction uses the vertex Ball out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L373-L379
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L373-L379

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

theorem Expanders.vertexBall_out : ∀ v ∈ vertexBall G u k, ∀ w, G.Adj v w → w ∉ vertexBall G u k →
    G.dist u v - 1 = k := by sorry
