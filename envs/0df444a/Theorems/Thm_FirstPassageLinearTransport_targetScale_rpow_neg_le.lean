-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_targetScale_rpow_neg_le
-- name    : FirstPassageLinearTransport.targetScale_rpow_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:08.844191+00:00
-- url     : https://prove2.me/theorems/0c186d0f-566a-4099-8a95-144dc13436b2
-- title:
--   First Passage Linear Transport: target Scale rpow neg le
-- statement:
--   The floor in `targetScale` costs at most one factor of two.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L259-L284
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L259-L284

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.targetScale_rpow_neg_le {r D : ℝ} {M : ℕ}
    (hr : 0 ≤ r) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (targetScale r M : ℝ) ^ (-D) ≤
      2 * Real.exp (-(r * D * M * Real.log 2)) := by sorry
