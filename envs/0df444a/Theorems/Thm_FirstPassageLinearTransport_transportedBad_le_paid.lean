-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_transportedBad_le_paid
-- name    : FirstPassageLinearTransport.transportedBad_le_paid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:30.308707+00:00
-- url     : https://prove2.me/theorems/a6bd9c42-7d21-56c5-a913-ca2bcb655544
-- title:
--   First Passage Linear Transport: transported Bad le paid
-- statement:
--   Pay the polynomial transport factor from the strict exponent gap
--   `chi < r`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L391-L441
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L391-L441

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.transportedBad_le_paid
    {r eta C D chi : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi : chi < r) {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by sorry
