-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_relabelRow
-- name    : Csg.MatrixGame.payoff_relabelRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:04:36.547714+00:00
-- url     : https://prove2.me/theorems/4b10fe0c-c6e5-4645-bc85-87e84bd81f16
-- title:
--   Matrix Game: payoff relabel Row
-- statement:
--   The relabelled game's payoff at any strategy pair is the original game's payoff at the row
--       strategy pulled back through `e.symm` -- the one computation everything else here reduces to,
--       a single reindexed `Finset.sum` (`Equiv.sum_comp`) inside `payoff_eq_sum_mul`'s already-summed
--       form.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L515-L520
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L515-L520

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

theorem Csg.MatrixGame.payoff_relabelRow (e : I' ≃ I) (x' : I' → ℝ) (y : J → ℝ) :
    (G.relabelRow e).payoff x' y = G.payoff (x' ∘ ⇑e.symm) y := by sorry
