-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_normalized_tail_le
-- name    : CohnElkies.saddleSourceGaussianKernel_normalized_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/d498b944-a02f-4158-9ee7-5f7225b04111
-- title:
--   CohnElkies.saddleSourceGaussianKernel_normalized_tail_le
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
open scoped Topology

theorem CohnElkies.saddleSourceGaussianKernel_normalized_tail_le
    {ε ℓ u z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hz : 0 ≤ z)
    (hlarge : 12 ≤ ℓ * saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
          saddleSourceGaussianKernel ε ℓ u T) ≤
        4 * Real.sqrt (2 * Real.pi) *
          Real.exp (-(z ^ 2) / 8) := by sorry
