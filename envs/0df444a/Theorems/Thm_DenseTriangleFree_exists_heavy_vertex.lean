-- Prove2me | Theorems.Thm_DenseTriangleFree_exists_heavy_vertex
-- name    : DenseTriangleFree.exists_heavy_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:50.147679+00:00
-- url     : https://prove2.me/theorems/4faebf9f-e4b9-4552-a634-832be5dec5ac
-- title:
--   Dense Triangle Free: exists heavy vertex
-- statement:
--   The Dense Triangle Free construction uses the exists heavy vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L100-L127
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L100-L127

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem DenseTriangleFree.exists_heavy_vertex (hδ : 10 * Fintype.card V < 29 * G.minDegree) {k : ℕ}
    (f : ℕ → V) (w : ℕ → ℕ) (hpos : 0 < ∑ i ∈ Finset.range k, w i) :
    ∃ y, 10 * ∑ i ∈ Finset.range k, w i <
      29 * ∑ i ∈ Finset.range k, (if G.Adj (f i) y then w i else 0) := by sorry
