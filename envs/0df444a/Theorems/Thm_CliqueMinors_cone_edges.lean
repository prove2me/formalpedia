-- Prove2me | Theorems.Thm_CliqueMinors_cone_edges
-- name    : CliqueMinors.cone_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:19.966413+00:00
-- url     : https://prove2.me/theorems/90359f95-7902-51c2-b5bd-d9b3332f5ae5
-- title:
--   Clique Minors: cone edges
-- statement:
--   The Clique Minors construction uses the cone edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L170-L186
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L170-L186

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.cone_edges {G : SimpleGraph V} {x : V} {m : ℕ}
    (hc : ∀ v, G.Adj x v → m ≤ (G.neighborFinset x ∩ G.neighborFinset v).card) :
    m * (G.neighborFinset x).card ≤ 2 * (coneG G x).edgeFinset.card := by sorry
