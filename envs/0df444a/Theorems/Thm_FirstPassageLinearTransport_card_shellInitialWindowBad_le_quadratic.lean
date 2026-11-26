-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_le_quadratic
-- name    : FirstPassageLinearTransport.card_shellInitialWindowBad_le_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:09.810684+00:00
-- url     : https://prove2.me/theorems/6a4908e4-2d3e-572b-9611-552106d61340
-- title:
--   First Passage Linear Transport: card shell Initial Window Bad le quadratic
-- statement:
--   All-shell quadratic exceptional count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L215-L266
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L215-L266

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_shellInitialWindowBad_le_quadratic
    {M : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by sorry
