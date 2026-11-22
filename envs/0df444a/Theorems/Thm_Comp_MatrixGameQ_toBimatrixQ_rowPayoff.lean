-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_rowPayoff
-- name    : Comp.MatrixGameQ.toBimatrixQ_rowPayoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:54.012968+00:00
-- url     : https://prove2.me/theorems/0a5ce600-1fe2-4a77-8283-4515b03c97d2
-- title:
--   Matrix Game Q: to Bimatrix Q row Payoff
-- statement:
--   The row player's payoff in the zero-sum bimatrix game is the negation of the column player's --
--       the zero-sum property at the level of mixed profiles.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L219-L221
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L219-L221

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.toBimatrixQ_rowPayoff (G : MatrixGameQ I J) (p : I → ℚ) (q : J → ℚ) :
    G.toBimatrixQ.rowPayoff p q = -(G.toBimatrixQ.colPayoff p q) := by sorry
