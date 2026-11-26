-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLossTotal_add
-- name    : FirstPassageLinearTransport.reverseLossTotal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:20.499391+00:00
-- url     : https://prove2.me/theorems/bc9abfb0-dd12-5c1b-8dcb-a20a615a9091
-- title:
--   First Passage Linear Transport: reverse Loss Total add
-- statement:
--   Total reverse loss is exactly additive under concatenation.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L57-L66
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L57-L66

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.reverseLossTotal_add (n k h : ℕ) :
    reverseLossTotal n (k + h) =
      reverseLossTotal n k + reverseLossTotal (orbit k n) h := by sorry
