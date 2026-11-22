-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_unique
-- name    : Csg.MatrixGame.value_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:18.483272+00:00
-- url     : https://prove2.me/theorems/c283c8de-9b52-4c71-b84d-4e35270c409c
-- title:
--   Matrix Game: value unique
-- statement:
--   The game's value doesn't depend on which saddle point exhibits it: *any* mixed-strategy pair
--       `p, q` satisfying the two no-unilateral-improvement conditions relative to each other has
--       `payoff p q = value`, not just the particular pair `value` was built from via
--       `Classical.choose`. Standard minimax fact (the *value* of a zero-sum game is unique even when
--       optimal strategies are not), proved directly from `value_row_optimal`/`value_col_optimal` by
--       chaining both pairs' optimality conditions against each other.
--
--       **Relocated here from `Basic.lean`**, which had itself relocated it from `MatchingPennies.lean`
--       once `MatrixGameMonotone.lean`'s `value_add_const` needed it too: a general fact about `value`
--       that doesn't depend on anything `CSG`- or worked-example-specific belongs beside `value` and
--       `exists_optimal_strategies` themselves, in the file that owns `MatrixGame`, not in a file about
--       a different structure built on top of it. Pure relocation, second hop -- the statement and
--       proof are unchanged from `Basic.lean`'s copy, which was itself unchanged from
--       `MatchingPennies.lean`'s original.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L235-L243
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L235-L243

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_unique {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I) (hq : q ∈ stdSimplex ℝ J)
    (hrow : ∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q)
    (hcol : ∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) :
    G.payoff p q = G.value := by sorry
