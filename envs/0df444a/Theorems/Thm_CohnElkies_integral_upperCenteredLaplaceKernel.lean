-- Prove2me | Theorems.Thm_CohnElkies_integral_upperCenteredLaplaceKernel
-- name    : CohnElkies.integral_upperCenteredLaplaceKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/62cab9ad-34b2-44dc-bd7e-804d486b46af
-- title:
--   CohnElkies.integral_upperCenteredLaplaceKernel
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

theorem CohnElkies.integral_upperCenteredLaplaceKernel
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperCenteredLaplaceKernel c T a) =
      Complex.log (c : ℂ) -
        Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹ := by sorry
