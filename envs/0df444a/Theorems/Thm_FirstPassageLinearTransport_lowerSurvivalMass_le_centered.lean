-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_centered
-- name    : FirstPassageLinearTransport.lowerSurvivalMass_le_centered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:48.962096+00:00
-- url     : https://prove2.me/theorems/6d01bbf8-4969-56bb-ac2f-23747cf7f0e5
-- title:
--   First Passage Linear Transport: lower Survival Mass le centered
-- statement:
--   Appendix B.1 in the `O((h+1)/sqrt n)` form consumed twice by the
--   three-block fixed-barrier argument.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L447-L489
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L447-L489

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.lowerSurvivalMass_le_centered
    {p v h : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hv : 0 < v) (hh : 0 ≤ h)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v)
    {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass p x (-h) n 0 ≤
      (1 + 2 / v) * (h + 1) / Real.sqrt n := by sorry
