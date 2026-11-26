-- Prove2me | Theorems.Thm_DenseTriangleFree_colorable_of_maximal
-- name    : DenseTriangleFree.colorable_of_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:07.876511+00:00
-- url     : https://prove2.me/theorems/0ba42fbc-a57c-53ee-9f0a-fa6feecdd12c
-- title:
--   Dense Triangle Free: colorable of maximal
-- statement:
--   **Step 2 of Jin's theorem.** A maximal triangle-free graph with `29 δ > 10 n` is
--   3-colourable.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L198-L205
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L198-L205

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem DenseTriangleFree.colorable_of_maximal [Fintype V] [DecidableRel G.Adj]
    (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by sorry
