-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_movingLow_admissible
-- name    : FirstPassageLinearTransport.eventually_movingLow_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:49.135024+00:00
-- url     : https://prove2.me/theorems/00bebd9d-d18b-52fe-a5ea-ba49d74e3053
-- title:
--   First Passage Linear Transport: eventually moving Low admissible
-- statement:
--   After one finite startup, all three moving low parameters lie in their
--   required open ranges and the affine-correction exponent is positive.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L212-L244
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L212-L244

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_movingLow_admissible
    {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) :
    ∀ᶠ L : ℕ in atTop,
      0 < movingLowTolerance K₀ L ∧
      movingLowTolerance K₀ L < driftGap ∧
      0 < movingLowRatio K₀ L ∧ movingLowRatio K₀ L < 1 ∧
      0 < movingLowLambda K₁ L ∧ movingLowLambda K₁ L < 1 ∧
      0 < a0 + movingLowTolerance K₀ L -
        2 * movingLowLambda K₁ L * movingLowTolerance K₀ L := by sorry
