-- Prove2me | Theorems.Thm_Expanders_vertexBall_parent
-- name    : Expanders.vertexBall_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:30.407605+00:00
-- url     : https://prove2.me/theorems/eaef48f7-24fa-440d-a5d5-efb0a154e7a1
-- title:
--   Expanders: vertex Ball parent
-- statement:
--   The Expanders construction uses the vertex Ball parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L387-L403
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L387-L403

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

theorem Expanders.vertexBall_parent [DecidableRel G.Adj] {d : ℕ} (hd : G.IsRegularOfDegree d) (hd1 : 1 ≤ d) :
    ∀ v ∈ vertexBall G u k, ∃ w ∈ vertexBall G u k, G.Adj v w ∧
      G.dist u w - 1 ≤ G.dist u v - 1 - 1 := by sorry
