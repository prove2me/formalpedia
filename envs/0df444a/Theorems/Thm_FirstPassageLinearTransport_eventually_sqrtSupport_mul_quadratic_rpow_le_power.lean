-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_quadratic_rpow_le_power
-- name    : FirstPassageLinearTransport.eventually_sqrtSupport_mul_quadratic_rpow_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:21:39.693553+00:00
-- url     : https://prove2.me/theorems/18ecf7ad-c28b-552d-a267-a85b725c4830
-- title:
--   First Passage Linear Transport: eventually sqrt Support mul quadratic rpow le power
-- statement:
--   Multiplying a quadratic rank factor and the compressed time support
--   costs only `5/2` powers, again with every strict margin available.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L169-L200
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L169-L200

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_sqrtSupport_mul_quadratic_rpow_le_power
    {p kappa : ℝ} (hkappa : kappa < p - 5 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 2) ^ (-p))) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by sorry
