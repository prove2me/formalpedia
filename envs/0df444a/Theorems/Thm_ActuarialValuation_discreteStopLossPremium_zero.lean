-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_zero
-- name    : ActuarialValuation.discreteStopLossPremium_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:34:06.022203+00:00
-- url     : https://prove2.me/theorems/11cf260f-dd25-4d94-adca-03ac76ee259d
-- title:
--   Zero attachment cedes the entire aggregate claim
-- statement:
--   With attachment zero the stop-loss reinsurer pays the entire realised nonnegative aggregate claim. The net reinsurance premium is therefore the gross mean of the aggregate distribution, not zero.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(0)=\mu_B
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean

namespace ActuarialValuation

theorem discreteStopLossPremium_zero (w : ℕ → ℝ) (bound : ℕ) :
  discreteStopLossPremium w bound 0 =
    discreteStopLossAggregateMean w bound := by sorry

end ActuarialValuation
