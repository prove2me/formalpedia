-- Prove2me | Theorems.Thm_DenseTriangleFree_heavy_step
-- name    : DenseTriangleFree.heavy_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:26.022249+00:00
-- url     : https://prove2.me/theorems/538b16f2-d0a0-4ee8-85bb-29b3041bff61
-- title:
--   Dense Triangle Free: heavy step
-- statement:
--   **Heavy step.** In a triangle-free graph with `29 δ > 10 n`, for vertices `f i` with weights
--   `ws`, known edges `edges` and forbidden sets `Fb` (no vertex sees all of a forbidden set), if the
--   check succeeds then some vertex sees all of some `J ∈ Js`.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L172-L213
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L172-L213

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.heavy_step {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree)
    (f : ℕ → V) (ws : List ℕ) (edges : List (ℕ × ℕ)) (Fb Js : List (List ℕ))
    (hE : ∀ e ∈ edges, G.Adj (f e.1) (f e.2))
    (hF : ∀ F ∈ Fb, ∀ y, (∀ i ∈ F, G.Adj (f i) y) → False)
    (hpos : 0 < ws.sum)
    (hc : heavyCheck ws edges Fb Js = true) :
    ∃ J ∈ Js, ∃ y, ∀ i ∈ J, G.Adj (f i) y := by sorry
