-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le_concrete
-- name    : FirstPassageLinearTransport.card_shellMaximalParityBad_le_concrete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:32.414409+00:00
-- url     : https://prove2.me/theorems/ad70b843-f78a-4e5e-bc7c-c6bce0f08e10
-- title:
--   First Passage Linear Transport: card shell Maximal Parity Bad le concrete
-- statement:
--   Concrete all-depth shell tail at the barrier height selected by `t`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L96-L140
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L96-L140

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_shellMaximalParityBad_le_concrete
    {M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ((shellMaximalParityBad M (maximalBarrierHeight t M)).card : ℝ) ≤
      2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by sorry
