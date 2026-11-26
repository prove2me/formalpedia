-- Prove2me | Theorems.Thm_DenseTriangleFree_pair_contra
-- name    : DenseTriangleFree.pair_contra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:43.722836+00:00
-- url     : https://prove2.me/theorems/0223d868-79e4-4f3c-8572-545d2b86822d
-- title:
--   Dense Triangle Free: pair contra
-- statement:
--   A pair with more than `m` witnessed indices contradicts the maximality of `m`.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Pairs.lean#L44-L57
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Pairs.lean#L44-L57

module
public import Mathlib
public import Definitions.Def_JinLib_Heavy
public import Definitions.Def_JinLib_Pairs
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

theorem DenseTriangleFree.pair_contra {m : ℕ}
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ m)
    (b w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0)
    (n0 : ¬ G.Adj b w0) (n1 : ¬ G.Adj b w1) (n2 : ¬ G.Adj b w2) (n3 : ¬ G.Adj b w3)
    (n4 : ¬ G.Adj b w4) (Q : Finset (Fin 5)) (hQ : m < Q.card)
    (hw : ∀ i ∈ Q, ∃ t, G.Adj b t ∧ G.Adj (![w0, w1, w2, w3, w4] (i - 1)) t ∧
      G.Adj (![w0, w1, w2, w3, w4] (i + 1)) t) : False := by sorry
