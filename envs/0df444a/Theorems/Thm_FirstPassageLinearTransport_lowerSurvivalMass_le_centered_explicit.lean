-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_centered_explicit
-- name    : FirstPassageLinearTransport.lowerSurvivalMass_le_centered_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:31:34.142582+00:00
-- url     : https://prove2.me/theorems/d3a58bc2-f480-4bb9-8a78-c6d8b71e586c
-- title:
--   First Passage Linear Transport: lower Survival Mass le centered explicit
-- statement:
--   The first, quantitative inequality in Appendix B.1, specialized to the
--   two-letter weighted walk used by the Collatz tilt.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L391-L443
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L391-L443

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.lowerSurvivalMass_le_centered_explicit
    {p v h : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hv : 0 < v) (hh : 0 ≤ h)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v)
    {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass p x (-h) n 0 ≤
      (h + 1) / (Real.sqrt n + h + 1) +
        (h + 1) * (Real.sqrt n + 1) / (v * n) := by sorry
