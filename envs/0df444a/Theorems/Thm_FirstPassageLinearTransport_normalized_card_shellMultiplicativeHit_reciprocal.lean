-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellMultiplicativeHit_reciprocal
-- name    : FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_reciprocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:38.150284+00:00
-- url     : https://prove2.me/theorems/25aed945-6332-4157-a722-c3aeaef60bfc
-- title:
--   First Passage Linear Transport: normalized card shell Multiplicative Hit reciprocal
-- statement:
--   The finite reciprocal maximum theorem transfers without loss to a
--   complete dyadic shell.  This is the shell form of the lower and upper bounds
--   used by the height obstruction.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L196-L205
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L196-L205

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_reciprocal
    {u : ℝ} (hu : 1 ≤ u) {M : ℕ} (hM : 0 < M)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (M : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (M : ℝ)) ≤
      ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ∧
    ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by sorry
