-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellMultiplicativeHit_quarter_le
-- name    : FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_quarter_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:29:14.365995+00:00
-- url     : https://prove2.me/theorems/a97745e2-31a9-446e-85dd-fbbd8452f232
-- title:
--   First Passage Linear Transport: normalized card shell Multiplicative Hit quarter le
-- statement:
--   The quarter-threshold normalization used by the manuscript contributes
--   the explicit shell exception `4/R`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L232-L240
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L232-L240

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_quarter_le
    {R : ℝ} (hR : 0 < R) (M : ℕ) :
    ((shellMultiplicativeHit M (R / 4)).card : ℝ) /
        (2 : ℝ) ^ M ≤ 4 / R := by sorry
