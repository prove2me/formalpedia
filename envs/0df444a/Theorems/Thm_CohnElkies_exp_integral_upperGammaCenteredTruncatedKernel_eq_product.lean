-- Prove2me | Theorems.Thm_CohnElkies_exp_integral_upperGammaCenteredTruncatedKernel_eq_product
-- name    : CohnElkies.exp_integral_upperGammaCenteredTruncatedKernel_eq_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/19c98453-78ff-4477-9880-df2f81979973
-- title:
--   CohnElkies.exp_integral_upperGammaCenteredTruncatedKernel_eq_product
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

theorem CohnElkies.exp_integral_upperGammaCenteredTruncatedKernel_eq_product
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (∏ k ∈ Finset.range (n + 1),
        ((((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) /
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
              (k : ℂ))))) *
        Complex.exp
          (-Complex.I *
            (((ℓ * T / 2 *
              (∑ k ∈ Finset.range (n + 1),
                (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by sorry
