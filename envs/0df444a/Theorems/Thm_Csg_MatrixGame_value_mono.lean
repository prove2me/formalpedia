-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_mono
-- name    : Csg.MatrixGame.value_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:53:06.976796+00:00
-- url     : https://prove2.me/theorems/e609b09d-5bfa-4f43-a1c7-9689ca6370fb
-- title:
--   Matrix Game: value mono
-- statement:
--   **The payoff.** The game's value is monotone in the payoff matrix: if row pays column at least
--       as much everywhere in `G'` as in `G`, then `G'`'s value is at least `G`'s. Proved by sandwiching
--       `G.value` between the two games evaluated at the *same* pair of strategies
--       (`G'.optimalRow, G.optimalCol`, belonging to neither game exclusively): `G`'s own saddle
--       condition bounds it above by that payoff (`value_row_optimal`), `payoff_mono` carries that bound
--       across to `G'`, and `G'`'s own saddle condition bounds the result above by `G'.value`
--       (`value_col_optimal`). Neither game's optimal strategies need to relate to the other's.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L308-L314
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L308-L314

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_mono {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) :
    G.value ≤ G'.value := by sorry
