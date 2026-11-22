-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
-- name    : Comp.MatrixGameQ.toMatrixGame_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:46.764808+00:00
-- url     : https://prove2.me/theorems/06df5431-81ce-44cc-a7dd-5033cd034c03
-- title:
--   Matrix Game Q: to Matrix Game A
-- statement:
--   The Matrix Game Q construction uses the to Matrix Game A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L116-L117
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L116-L117

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.toMatrixGame_A (G : MatrixGameQ I J) (i : I) (j : J) :
    G.toMatrixGame.A i j = ((G.A i j : ℚ) : ℝ) := by sorry

attribute [defeq] Comp.MatrixGameQ.toMatrixGame_A
