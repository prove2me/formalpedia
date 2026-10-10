-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_increment
-- name    : ActuarialValuation.discreteStopLossPremium_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:37:50.450332+00:00
-- url     : https://prove2.me/theorems/65df2dbf-9149-410a-9f12-26aa142b9a95
-- title:
--   Raising attachment by one saves the strict loss tail probability
-- statement:
--   Raising the deductible by one unit reduces the payment by exactly one for every loss strictly above the old attachment and by zero otherwise. Taking the weighted sum yields the exact adjacent-attachment premium difference, valid for any real mass coefficients.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(d)-\Pi_B(d+1)=T_B(d)
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossPremium_increment
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossPremium w bound deductible =
    discreteStopLossPremium w bound (deductible + 1) +
      discreteStopLossTail w bound deductible := by sorry

end ActuarialValuation
