-- Prove2me | Theorems.Thm_CohnElkies_exp_integral_upperCenteredLaplaceKernel_scale
-- name    : CohnElkies.exp_integral_upperCenteredLaplaceKernel_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/89871806-33e8-4c6a-bb9f-fe1daa1aea0d
-- title:
--   CohnElkies.exp_integral_upperCenteredLaplaceKernel_scale
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

theorem CohnElkies.exp_integral_upperCenteredLaplaceKernel_scale
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      (((s * c : ℝ) : ℂ) /
          (((s * c : ℝ) : ℂ) -
            Complex.I * ((s * T : ℝ) : ℂ))) *
        Complex.exp
          (-Complex.I *
            (((s * T / (s * c) : ℝ) : ℂ))) := by sorry
