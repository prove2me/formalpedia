-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_sqrt_mul_log_rpow_le
-- name    : FirstPassageLinearTransport.eventually_sqrt_mul_log_rpow_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:37.058962+00:00
-- url     : https://prove2.me/theorems/3921ff91-aabd-5dcf-b871-fccb30ef05b3
-- title:
--   First Passage Linear Transport: eventually sqrt mul log rpow le
-- statement:
--   A square-root logarithmic prefactor costs only one half power, with every
--   strict exponent below that endpoint available eventually.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L26-L66
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L26-L66

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_sqrt_mul_log_rpow_le
    {p kappa : ℝ} (hkappa : kappa < p - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 2) ^ (-p)) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by sorry
