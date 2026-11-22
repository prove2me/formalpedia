-- Prove2me | Theorems.Thm_Csg_MatrixGame_mem_stdSimplex_comp_symm
-- name    : Csg.MatrixGame.mem_stdSimplex_comp_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:03:59.499261+00:00
-- url     : https://prove2.me/theorems/cd35b0db-f321-4c8a-b252-180236763354
-- title:
--   Matrix Game: mem std Simplex comp symm
-- statement:
--   A strategy on the relabelled row type transports to one on the original, by pushing along
--       `e.symm`. Needed below to check that a strategy is optimal for the *original* game once it's
--       been pulled back from a candidate on `I'`.
--
--       Pure `stdSimplex`-membership bookkeeping (a nonnegativity fact plus a reindexed sum), needing
--       only `Fintype I`/`Fintype I'` for `Equiv.sum_comp` -- the `Nonempty`/`DecidableEq` instance
--       arguments on both action types go unused here, which is what the `omit` above drops.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L496-L499
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L496-L499

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
omit [Nonempty I] [DecidableEq I] [Nonempty I'] [DecidableEq I']

theorem Csg.MatrixGame.mem_stdSimplex_comp_symm (e : I' ≃ I) {x' : I' → ℝ} (hx' : x' ∈ stdSimplex ℝ I') :
    x' ∘ ⇑e.symm ∈ stdSimplex ℝ I := by sorry
