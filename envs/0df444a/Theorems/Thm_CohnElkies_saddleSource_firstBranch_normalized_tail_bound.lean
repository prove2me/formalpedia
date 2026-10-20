-- Prove2me | Theorems.Thm_CohnElkies_saddleSource_firstBranch_normalized_tail_bound
-- name    : CohnElkies.saddleSource_firstBranch_normalized_tail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/e93f5f86-0116-4e73-a089-13cc842963f5
-- title:
--   CohnElkies.saddleSource_firstBranch_normalized_tail_bound
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddleSource_firstBranch_normalized_tail_bound
    {ε ℓ u z C : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hC : 0 < C)
    (hupper :
      (1 + u) * saddleSourceGaussianVariance ε ℓ u ≤ C)
    (hz : 0 ≤ z)
    (hquadratic :
      6 ≤ (ε * ℓ / (2 * Real.exp 1)) / (1 + u))
    (hlinear : 6 ≤ ε * ℓ / (2 * Real.exp 1)) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt
          (Real.pi * C / (ε / (2 * Real.exp 1))) *
        Real.exp
          (-(ε / (2 * Real.exp 1) / (4 * C)) * z ^ 2) +
        (16 / (ε / (2 * Real.exp 1))) *
          Real.sqrt (C / (ℓ * (1 + u))) := by sorry
