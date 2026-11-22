-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_value_eq_of_nashCert
-- name    : Comp.MatrixGameQ.value_eq_of_nashCert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:45:29.037936+00:00
-- url     : https://prove2.me/theorems/fd2a8e21-1efe-472d-98a6-65b593fd420d
-- title:
--   Matrix Game Q: value eq of nash Cert
-- statement:
--   The matrix game's value, read off a Nash certificate for its bimatrix form. The composition of
--       `valueCert_of_nashCert` with `value_eq_of_valueCert`, recorded so the equilibria line can use
--       one name.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L245-L248
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L245-L248

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.value_eq_of_nashCert {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.toMatrixGame.value = ((G.toBimatrixQ.colPayoff p q : ℚ) : ℝ) := by sorry
