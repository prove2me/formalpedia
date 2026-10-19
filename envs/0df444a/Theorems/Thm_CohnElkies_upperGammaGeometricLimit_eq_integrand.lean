-- Prove2me | Theorems.Thm_CohnElkies_upperGammaGeometricLimit_eq_integrand
-- name    : CohnElkies.upperGammaGeometricLimit_eq_integrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/d51aa494-cfd9-4db7-837e-453a3abc7133
-- title:
--   CohnElkies.upperGammaGeometricLimit_eq_integrand
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
open scoped Topology BigOperators

theorem CohnElkies.upperGammaGeometricLimit_eq_integrand
    (ℓ η T a : ℝ) :
    upperCosLaplaceKernel η T a *
        (1 - Real.exp (-(2 * a / ℓ)))⁻¹ =
      upperGammaDampingIntegrand ℓ η T a := by sorry
