-- Prove2me | Theorems.Thm_CohnElkies_stripHolomorphicPoissonKernel_eq_scaled
-- name    : CohnElkies.stripHolomorphicPoissonKernel_eq_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/25109f72-0445-4eb6-a230-06ced4f7f9a3
-- title:
--   CohnElkies.stripHolomorphicPoissonKernel_eq_scaled
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

theorem CohnElkies.stripHolomorphicPoissonKernel_eq_scaled
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s y : ℝ) :
    stripHolomorphicPoissonKernel ℓ
        ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y =
      stripComplexPoissonKernel σ ((s - y) / ℓ) / (ℓ : ℂ) := by sorry
