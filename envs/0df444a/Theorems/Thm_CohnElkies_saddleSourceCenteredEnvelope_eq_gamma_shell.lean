-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_eq_gamma_shell
-- name    : CohnElkies.saddleSourceCenteredEnvelope_eq_gamma_shell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/3ff5f42f-528e-4411-a5e2-def97e0e5b93
-- title:
--   CohnElkies.saddleSourceCenteredEnvelope_eq_gamma_shell
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

theorem CohnElkies.saddleSourceCenteredEnvelope_eq_gamma_shell
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (v T : ℝ) :
    saddleSourceCenteredEnvelope ε ℓ u v T =
      (Complex.Gamma
          (((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) /
        (Real.Gamma (ℓ * (1 + u) / 2) : ℂ)) *
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
      (Complex.exp
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ))) := by sorry
