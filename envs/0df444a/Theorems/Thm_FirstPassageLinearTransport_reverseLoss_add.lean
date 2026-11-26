-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLoss_add
-- name    : FirstPassageLinearTransport.reverseLoss_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:22.989811+00:00
-- url     : https://prove2.me/theorems/9c3b66db-7c0a-497e-9f14-5918fdddccaa
-- title:
--   First Passage Linear Transport: reverse Loss add
-- statement:
--   Reverse loss is shift-covariant under an orbit prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L46-L49
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L46-L49

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.reverseLoss_add (n k j : ℕ) :
    reverseLoss n (k + j) = reverseLoss (orbit k n) j := by sorry
