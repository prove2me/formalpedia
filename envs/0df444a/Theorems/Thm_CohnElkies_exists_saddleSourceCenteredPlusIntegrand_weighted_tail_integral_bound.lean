-- Prove2me | Theorems.Thm_CohnElkies_exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
-- name    : CohnElkies.exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/145d8579-0276-47a6-b765-df28d1f69f0f
-- title:
--   CohnElkies.exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
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

theorem CohnElkies.exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, -1 < u →
          ∀ v R : ℝ,
            Integrable (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T)) →
            (∫ T : ℝ in saddleGaussianTailSet R,
              ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) ≤
              C * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ in saddleGaussianTailSet R,
                  saddleGaussianTailWeight T *
                    Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by sorry
