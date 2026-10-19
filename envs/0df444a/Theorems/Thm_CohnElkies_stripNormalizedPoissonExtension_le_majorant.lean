-- Prove2me | Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant
-- name    : CohnElkies.stripNormalizedPoissonExtension_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/f1b0539e-4606-4ccb-b1ea-049d566e68ca
-- title:
--   CohnElkies.stripNormalizedPoissonExtension_le_majorant
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

theorem CohnElkies.stripNormalizedPoissonExtension_le_majorant
    {σ : ℝ} (hzero : 0 ≤ σ) (hone : σ ≤ 1) (T : ℝ) :
    0 ≤ stripNormalizedPoissonExtension σ T ∧
      stripNormalizedPoissonExtension σ T ≤
        stripPoissonExponentialMajorant T := by sorry
