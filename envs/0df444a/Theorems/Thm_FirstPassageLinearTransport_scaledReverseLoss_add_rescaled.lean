-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_add_rescaled
-- name    : FirstPassageLinearTransport.scaledReverseLoss_add_rescaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:26.58111+00:00
-- url     : https://prove2.me/theorems/5854e3c0-1179-5de3-8a98-e4135073bba2
-- title:
--   First Passage Linear Transport: scaled Reverse Loss add rescaled
-- statement:
--   Exact rescaling of concatenated loss.  Earlier block loss is suppressed by
--   the ratio of the later threshold to the earlier one.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L70-L78
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L70-L78

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.scaledReverseLoss_add_rescaled
    {Ylo Yhi : ℕ} (n k h : ℕ) (hYhi : 0 < Yhi) :
    scaledReverseLoss Ylo n (k + h) =
      (Ylo : ℚ) / (Yhi : ℚ) * scaledReverseLoss Yhi n k +
        scaledReverseLoss Ylo (orbit k n) h := by sorry
