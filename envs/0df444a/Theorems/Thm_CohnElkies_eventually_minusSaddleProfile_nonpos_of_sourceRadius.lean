-- Prove2me | Theorems.Thm_CohnElkies_eventually_minusSaddleProfile_nonpos_of_sourceRadius
-- name    : CohnElkies.eventually_minusSaddleProfile_nonpos_of_sourceRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.654547+00:00
-- url     : https://prove2.me/theorems/f4a2b354-67c0-4ad2-8b32-9ff562b3f843
-- title:
--   CohnElkies.eventually_minusSaddleProfile_nonpos_of_sourceRadius
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
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.eventually_minusSaddleProfile_nonpos_of_sourceRadius :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSourceRadius ε d ≤ r →
            (minusSaddleProfile ε ((d : ℝ) / 2) r).re ≤ 0 := by sorry
