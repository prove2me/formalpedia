-- Prove2me | Theorems.Thm_Expanders_nilli_vertexBall
-- name    : Expanders.nilli_vertexBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:31.841823+00:00
-- url     : https://prove2.me/theorems/32a6d1fe-309e-488a-9376-d36fdb84b5db
-- title:
--   Expanders: nilli vertex Ball
-- statement:
--   Nilli's estimate for the test vector on the ball of radius `k + 1` around a vertex.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L406-L415
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L406-L415

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}

theorem Expanders.nilli_vertexBall [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d) (hd : G.IsRegularOfDegree d)
    (u : V) (k : ℕ) :
    (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) *
        dotProduct (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1))
          (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1)) ≤
      dotProduct (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1))
        (G.adjMatrix ℝ *ᵥ
          nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1)) := by sorry
