-- Prove2me | Theorems.Thm_DenseTriangleFree_patZ_013_of
-- name    : DenseTriangleFree.patZ_013_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:33.361846+00:00
-- url     : https://prove2.me/theorems/ca22eb83-86df-5816-8db0-14f8dc190f3c
-- title:
--   Dense Triangle Free: pat Z 013 of
-- statement:
--   The Dense Triangle Free construction uses the pat Z 013 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Patterns.lean#L299-L316
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Patterns.lean#L299-L316

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

theorem DenseTriangleFree.patZ_013_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 3} : Finset (Fin 5))) :
    False := by sorry
