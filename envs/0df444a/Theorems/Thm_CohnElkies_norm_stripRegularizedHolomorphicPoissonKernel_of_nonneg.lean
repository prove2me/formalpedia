-- Prove2me | Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
-- name    : CohnElkies.norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/2de93367-75cd-4281-98f3-6594c7e69980
-- title:
--   CohnElkies.norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
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

theorem CohnElkies.norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : 0 ≤ y) :
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by sorry
