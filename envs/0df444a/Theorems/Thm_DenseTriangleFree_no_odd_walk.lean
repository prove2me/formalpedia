-- Prove2me | Theorems.Thm_DenseTriangleFree_no_odd_walk
-- name    : DenseTriangleFree.no_odd_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:07.827682+00:00
-- url     : https://prove2.me/theorems/aa3fcbdd-dc0f-47ec-b62d-266abd9308d8
-- title:
--   Dense Triangle Free: no odd walk
-- statement:
--   **No odd closed walk avoids the neighbourhood of a vertex.**
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L61-L153
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L61-L153

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

theorem DenseTriangleFree.no_odd_walk (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a : V) (m : ℕ) : ∀ c : ℕ → V, (∀ i, c (i + m) = c i) → (∀ i, G.Adj (c i) (c (i + 1))) →
      (∀ i, ¬ G.Adj a (c i)) → Odd m → False := by sorry
