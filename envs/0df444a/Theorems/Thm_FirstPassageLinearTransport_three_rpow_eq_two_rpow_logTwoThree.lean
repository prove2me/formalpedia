-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree
-- name    : FirstPassageLinearTransport.three_rpow_eq_two_rpow_logTwoThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:40.42589+00:00
-- url     : https://prove2.me/theorems/a6f30904-fa7c-59d2-9dbc-db887fa48c76
-- title:
--   First Passage Linear Transport: three rpow eq two rpow log Two Three
-- statement:
--   Change of base specialized to `log₂ 3`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L282-L290
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L282-L290

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.three_rpow_eq_two_rpow_logTwoThree (x : ℝ) :
    (3 : ℝ) ^ x = (2 : ℝ) ^ (logTwoThree * x) := by sorry
