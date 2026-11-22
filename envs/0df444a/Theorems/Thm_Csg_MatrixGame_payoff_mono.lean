-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_mono
-- name    : Csg.MatrixGame.payoff_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:02:41.11254+00:00
-- url     : https://prove2.me/theorems/2bcf9f8c-3433-4ae6-be12-389b83c6bc3e
-- title:
--   Matrix Game: payoff mono
-- statement:
--   `payoff` is monotone in the payoff matrix, for any fixed pair of nonnegative (not necessarily
--       normalised, not necessarily optimal) strategies -- a direct term-by-term comparison of the
--       bilinear extension. Not needed by anything built so far; `value_mono` below is the only
--       consumer, comparing two different games' values via a shared pair of strategies belonging to
--       neither game in particular.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L294-L299
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L294-L299

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.payoff_mono {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) {x : I → ℝ}
    {y : J → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    G.payoff x y ≤ G'.payoff x y := by sorry
