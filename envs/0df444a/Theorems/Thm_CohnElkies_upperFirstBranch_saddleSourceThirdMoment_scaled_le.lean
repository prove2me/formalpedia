-- Prove2me | Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceThirdMoment_scaled_le
-- name    : CohnElkies.upperFirstBranch_saddleSourceThirdMoment_scaled_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/b39ed3aa-3a79-445b-b4e4-e9410457b239
-- title:
--   CohnElkies.upperFirstBranch_saddleSourceThirdMoment_scaled_le
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
open Filter Set MeasureTheory intervalIntegral
open scoped Topology

theorem CohnElkies.upperFirstBranch_saddleSourceThirdMoment_scaled_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    (1 + u) ^ 2 * upperSaddleThirdMoment ε ℓ (u - 1) ≤
      saddleSourceFirstBranchThirdMomentCoefficient ε := by sorry
