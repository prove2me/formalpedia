-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_IsFirstPassage_nested
-- name    : FirstPassageLinearTransport.IsFirstPassage.nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:14.576064+00:00
-- url     : https://prove2.me/theorems/8e018b3d-c394-5a3f-8bb7-abade0d28a49
-- title:
--   Is First Passage: nested
-- statement:
--   Concatenating a first passage through a lower threshold to a first passage
--   through a higher threshold produces a direct first passage of the original
--   source through the lower threshold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L25-L43
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L25-L43

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.IsFirstPassage.nested
    {Ylo Yhi n t h : ℕ}
    (hthreshold : Ylo < Yhi)
    (hhi : IsFirstPassage Yhi n t)
    (hlo : IsFirstPassage Ylo (orbit t n) h) :
    IsFirstPassage Ylo n (t + h) := by sorry
