-- Prove2me | Theorems.Thm_CohnElkies_exp_saddleSourceShellCenteredPhase
-- name    : CohnElkies.exp_saddleSourceShellCenteredPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/01a086fa-2c5e-4976-b88f-d9ef7537430e
-- title:
--   CohnElkies.exp_saddleSourceShellCenteredPhase
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

theorem CohnElkies.exp_saddleSourceShellCenteredPhase
    (ε ℓ u T : ℝ) :
    Complex.exp (saddleSourceShellCenteredPhase ε ℓ u T) =
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by sorry
