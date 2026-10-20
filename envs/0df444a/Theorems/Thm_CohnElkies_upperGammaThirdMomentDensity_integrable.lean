-- Prove2me | Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_integrable
-- name    : CohnElkies.upperGammaThirdMomentDensity_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/89e374c1-b0ee-4d2a-944d-ce5b7e6441d9
-- title:
--   CohnElkies.upperGammaThirdMomentDensity_integrable
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

theorem CohnElkies.upperGammaThirdMomentDensity_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by sorry
