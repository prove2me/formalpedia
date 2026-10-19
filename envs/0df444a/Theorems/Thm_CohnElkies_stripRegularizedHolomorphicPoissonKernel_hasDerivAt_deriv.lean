-- Prove2me | Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
-- name    : CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/aad64941-c106-456d-bd56-ad484da55c66
-- title:
--   CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
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

theorem CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) z := by sorry
