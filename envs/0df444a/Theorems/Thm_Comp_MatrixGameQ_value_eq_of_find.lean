-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_value_eq_of_find
-- name    : Comp.MatrixGameQ.value_eq_of_find
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:11:22.683923+00:00
-- url     : https://prove2.me/theorems/a5953e13-6a83-44af-b352-4c2a410dc9e9
-- title:
--   Matrix Game Q: value eq of find
-- statement:
--   **The payoff.** A successful search pins the real-valued game value exactly. Composition of
--       `valueCert_of_find` with `MatrixGameQ.value_eq_of_valueCert`; no new mathematics, and in
--       particular no appeal to the solver being right.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Search.lean#L188-L191
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Search.lean#L188-L191

import Definitions.Def_Comp_MatrixGameQ
import Definitions.Def_Comp_Search
set_option autoImplicit true
open Comp
open Csg
open Comp.MatrixGameQ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

theorem Comp.MatrixGameQ.value_eq_of_find {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.toMatrixGame.value = ((t : ℚ) : ℝ) := by sorry
