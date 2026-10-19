-- Prove2me | Theorems.Thm_CohnElkies_stripHolomorphicPoissonKernel_denominator_ne_zero
-- name    : CohnElkies.stripHolomorphicPoissonKernel_denominator_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/9a468754-0fce-4fdf-a9d2-9973927325bd
-- title:
--   CohnElkies.stripHolomorphicPoissonKernel_denominator_ne_zero
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

theorem CohnElkies.stripHolomorphicPoissonKernel_denominator_ne_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Complex.exp
      (((Real.pi : ℂ) *
        (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
          (2 * (ℓ : ℂ))) - 1 ≠ 0 := by sorry
