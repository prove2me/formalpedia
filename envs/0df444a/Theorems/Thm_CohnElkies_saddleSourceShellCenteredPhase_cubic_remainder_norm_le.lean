-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceShellCenteredPhase_cubic_remainder_norm_le
-- name    : CohnElkies.saddleSourceShellCenteredPhase_cubic_remainder_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/2c2493b0-cb46-41a7-aef9-8c0179c03bd3
-- title:
--   CohnElkies.saddleSourceShellCenteredPhase_cubic_remainder_norm_le
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

theorem CohnElkies.saddleSourceShellCenteredPhase_cubic_remainder_norm_le
    {ε ℓ : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (u T : ℝ) :
    ‖saddleSourceShellCenteredPhase ε ℓ u T +
        ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
          T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
        |T| ^ 3 := by sorry
