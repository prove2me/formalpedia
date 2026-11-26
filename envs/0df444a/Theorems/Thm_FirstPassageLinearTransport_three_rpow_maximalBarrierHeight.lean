-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_three_rpow_maximalBarrierHeight
-- name    : FirstPassageLinearTransport.three_rpow_maximalBarrierHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:06.050016+00:00
-- url     : https://prove2.me/theorems/ca5b37cf-a629-5bfc-8d9b-71426ea0f197
-- title:
--   First Passage Linear Transport: three rpow maximal Barrier Height
-- statement:
--   The First Passage Linear Transport construction uses the three rpow maximal Barrier Height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L356-L363
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L356-L363

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.three_rpow_maximalBarrierHeight (t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ maximalBarrierHeight t M =
      (2 : ℝ) ^ (t * (M : ℝ) / 2) := by sorry
