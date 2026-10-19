-- Prove2me | Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_hasDerivAt
-- name    : CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/097c2874-f0db-408a-9304-f48d01e8b01c
-- title:
--   CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology

theorem CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (-(Complex.I * (Real.pi : ℂ) *
          stripSchwarzExponential ℓ z y) /
        (4 * (ℓ : ℂ) ^ 2 *
          (stripSchwarzExponential ℓ z y - 1) ^ 2)) z := by sorry
