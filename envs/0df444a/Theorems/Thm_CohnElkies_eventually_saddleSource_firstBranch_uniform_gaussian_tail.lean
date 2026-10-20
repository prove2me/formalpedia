-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSource_firstBranch_uniform_gaussian_tail
-- name    : CohnElkies.eventually_saddleSource_firstBranch_uniform_gaussian_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/00ca7515-331c-439c-8979-66276a98905a
-- title:
--   CohnElkies.eventually_saddleSource_firstBranch_uniform_gaussian_tail
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

theorem CohnElkies.eventually_saddleSource_firstBranch_uniform_gaussian_tail :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ,
            -1 < u → u ≤ 1 + ε / 2 →
              Real.log ℓ / 4 ≤ ℓ * (1 + u) →
                Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    saddleSourceGaussianKernel ε ℓ u T) < κ := by sorry
