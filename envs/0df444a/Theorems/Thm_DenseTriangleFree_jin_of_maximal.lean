-- Prove2me | Theorems.Thm_DenseTriangleFree_jin_of_maximal
-- name    : DenseTriangleFree.jin_of_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:59.59316+00:00
-- url     : https://prove2.me/theorems/5ab1b5b5-54a7-55cb-8ac8-c4cf3b31fbb5
-- title:
--   Dense Triangle Free: jin of maximal
-- statement:
--   **Step 0 of Jin's theorem.** It suffices to prove Jin's theorem for maximal triangle-free
--   graphs: if every maximal triangle-free graph `G'` on `V` with `29 δ(G') > 10 |V|` is 3-colourable,
--   then so is every triangle-free graph `G` on `V` with `29 δ(G) > 10 |V|`.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Maximal.lean#L74-L84
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Maximal.lean#L74-L84

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Maximal
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*}

theorem DenseTriangleFree.jin_of_maximal [Fintype V]
    (hcore : ∀ G' : SimpleGraph V, [DecidableRel G'.Adj] →
      Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G' →
      10 * Fintype.card V < 29 * G'.minDegree → G'.Colorable 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.CliqueFree 3)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by sorry
