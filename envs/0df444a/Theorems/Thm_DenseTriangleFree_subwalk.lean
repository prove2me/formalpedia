-- Prove2me | Theorems.Thm_DenseTriangleFree_subwalk
-- name    : DenseTriangleFree.subwalk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:38.25766+00:00
-- url     : https://prove2.me/theorems/9516a4a3-3cd8-532d-8d92-2b0325c7f7fa
-- title:
--   Dense Triangle Free: subwalk
-- statement:
--   A segment `c s, …, c (s + L - 1)` of a closed walk, closed up by an edge, is a closed walk.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L51-L58
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L51-L58

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

theorem DenseTriangleFree.subwalk {a : V} {c : ℕ → V} (hc : ∀ i, G.Adj (c i) (c (i + 1)))
    (hn : ∀ i, ¬ G.Adj a (c i)) (s L : ℕ) (hL : 0 < L) (hch : G.Adj (c (s + L - 1)) (c s)) :
    (∀ i, c (s + (i + L) % L) = c (s + i % L)) ∧
    (∀ i, G.Adj (c (s + i % L)) (c (s + (i + 1) % L))) ∧ ∀ i, ¬ G.Adj a (c (s + i % L)) := by sorry
