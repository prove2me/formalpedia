-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceStationaryFrequencyPhase_eq
-- name    : CohnElkies.saddleSourceStationaryFrequencyPhase_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/ee6bdfd6-e561-4356-81c0-fc055c61fd16
-- title:
--   CohnElkies.saddleSourceStationaryFrequencyPhase_eq
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

theorem CohnElkies.saddleSourceStationaryFrequencyPhase_eq
    (ε ℓ u T : ℝ) :
    Complex.exp
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T *
            saddleSourceStationaryLogRadius ε ℓ u : ℝ) : ℂ)) =
    Complex.exp
        (Complex.I *
          ((ℓ * T / 2 *
            saddleDigamma (ℓ * (1 + u) / 2) : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by sorry
