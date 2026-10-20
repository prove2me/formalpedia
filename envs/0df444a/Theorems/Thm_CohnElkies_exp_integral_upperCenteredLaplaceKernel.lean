-- Prove2me | Theorems.Thm_CohnElkies_exp_integral_upperCenteredLaplaceKernel
-- name    : CohnElkies.exp_integral_upperCenteredLaplaceKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/9def5589-883f-466b-8f41-2a275a38c5bc
-- title:
--   CohnElkies.exp_integral_upperCenteredLaplaceKernel
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

theorem CohnElkies.exp_integral_upperCenteredLaplaceKernel
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      ((c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ))) *
        Complex.exp
          (-Complex.I * ((T / c : ℝ) : ℂ)) := by sorry
