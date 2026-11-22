-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_sum_col
-- name    : Comp.MatrixGameQ.toBimatrixQ_sum_col
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:53.5995+00:00
-- url     : https://prove2.me/theorems/c37ed796-1676-4d97-92c4-d78e2bc4ff8c
-- title:
--   Matrix Game Q: to Bimatrix Q sum col
-- statement:
--   A pure column's payment is unchanged by the embedding, since `C = A`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L224-L225
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L224-L225

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.toBimatrixQ_sum_col (G : MatrixGameQ I J) (p : I → ℚ) (j : J) :
    ∑ i, p i * G.toBimatrixQ.C i j = ∑ i, p i * G.A i j := by sorry
