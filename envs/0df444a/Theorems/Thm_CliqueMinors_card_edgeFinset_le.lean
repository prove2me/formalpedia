-- Prove2me | Theorems.Thm_CliqueMinors_card_edgeFinset_le
-- name    : CliqueMinors.card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:40.647922+00:00
-- url     : https://prove2.me/theorems/996bc356-8f88-4d98-8e78-21f21bac79c3
-- title:
--   Clique Minors: card edge Finset le
-- statement:
--   A finite graph on `n ≥ 2` vertices without a `K₄` minor has at most `2n - 3` edges.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L753-L761
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L753-L761

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}

theorem CliqueMinors.card_edgeFinset_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by sorry
