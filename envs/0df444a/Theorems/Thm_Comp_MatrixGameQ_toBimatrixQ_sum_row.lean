-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_sum_row
-- name    : Comp.MatrixGameQ.toBimatrixQ_sum_row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:42.877565+00:00
-- url     : https://prove2.me/theorems/deb9658c-2fae-4281-a278-0b4b7ffec239
-- title:
--   Matrix Game Q: to Bimatrix Q sum row
-- statement:
--   A pure row's payoff in the zero-sum bimatrix game is the negation of its payment. The two
--       `simp` calls here and in the next lemma are deliberately left without an explicit
--       sum-of-negations lemma name: the fact is in `simp`'s default set, and naming it wrongly would
--       be an unknown-constant error rather than an unsolved goal.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L213-L215
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L213-L215

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.toBimatrixQ_sum_row (G : MatrixGameQ I J) (q : J → ℚ) (i : I) :
    ∑ j, G.toBimatrixQ.R i j * q j = -(∑ j, G.A i j * q j) := by sorry
