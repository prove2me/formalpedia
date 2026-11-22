-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_valueCert_of_find
-- name    : Comp.MatrixGameQ.valueCert_of_find
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:59.847802+00:00
-- url     : https://prove2.me/theorems/155083cb-a68e-450e-a4bb-d7c3211ba920
-- title:
--   Matrix Game Q: value Cert of find
-- statement:
--   Whatever the search returns really is a value certificate. This is the only place the search and
--       the proofs meet, and it says nothing about the search being *complete* -- only that it does not
--       lie.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Search.lean#L177-L183
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Search.lean#L177-L183

import Definitions.Def_Comp_MatrixGameQ
import Definitions.Def_Comp_Search
set_option autoImplicit true
open Comp
open Csg
open Comp.MatrixGameQ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

theorem Comp.MatrixGameQ.valueCert_of_find {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.ValueCert t p q := by sorry
