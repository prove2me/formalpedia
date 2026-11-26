-- Prove2me | Theorems.Thm_DenseTriangleFree_patZ_013
-- name    : DenseTriangleFree.patZ_013
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:00.524682+00:00
-- url     : https://prove2.me/theorems/05d88fe4-6ceb-5db6-b75e-504761c6dee2
-- title:
--   Dense Triangle Free: pat Z 013
-- statement:
--   The Dense Triangle Free construction uses the pat Z 013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Patterns.lean#L224-L297
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Patterns.lean#L224-L297

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
  (hδ : 10 * Fintype.card V < 29 * G.minDegree)
include h3 hmax hδ

theorem DenseTriangleFree.patZ_013 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_3 : ¬ G.Adj x0 x3)
    (n_0_4 : ¬ G.Adj x0 x4) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6)
    (h_0_7 : G.Adj x0 x7) (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8)
    (h_3_8 : G.Adj x3 x8) (h_5_8 : G.Adj x5 x8)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by sorry
