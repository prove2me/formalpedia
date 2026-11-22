-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_relabelCol
-- name    : Csg.MatrixGame.payoff_relabelCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:05:01.384905+00:00
-- url     : https://prove2.me/theorems/1dbffff0-9f49-4760-80ff-d19ba17701d6
-- title:
--   Matrix Game: payoff relabel Col
-- statement:
--   The relabelled game's payoff at any strategy pair is the original game's payoff at the column
--       strategy pulled back through `e.symm` -- mirror of `payoff_relabelRow`, via
--       `payoff_eq_sum_mul'` instead of `payoff_eq_sum_mul`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L598-L603
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L598-L603

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']

theorem Csg.MatrixGame.payoff_relabelCol (e : J' ≃ J) (x : I → ℝ) (y' : J' → ℝ) :
    (G.relabelCol e).payoff x y' = G.payoff x (y' ∘ ⇑e.symm) := by sorry
