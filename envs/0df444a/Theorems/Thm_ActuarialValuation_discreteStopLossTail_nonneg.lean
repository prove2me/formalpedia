-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossTail_nonneg
-- name    : ActuarialValuation.discreteStopLossTail_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:37:13.152478+00:00
-- url     : https://prove2.me/theorems/471f2011-ffb4-444d-9db4-5884fce6d7d6
-- title:
--   Aggregate tail probability is nonnegative
-- statement:
--   The tail is an indicator-weighted sum over discrete losses above the attachment point. Every included probability mass is nonnegative, so the total excess-claim probability is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   w_s\ge0\Longrightarrow T_B(d)\ge0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossTail_nonneg
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ discreteStopLossTail w bound deductible := by sorry

end ActuarialValuation
