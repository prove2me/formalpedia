-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossLimitedMean_bridge
-- name    : ActuarialValuation.discreteStopLossLimitedMean_bridge
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:48:15.805559+00:00
-- url     : https://prove2.me/theorems/e3e47b0b-5439-4118-be0d-b4a35b087538
-- title:
--   Expected retained layer plus ceded stop-loss premium equals gross mean
-- statement:
--   The gross loss is partitioned event by event into the retained capped layer and the excess layer. Taking the finite expectation of both parts preserves this equality, so the insurer's limited expected value plus the pure reinsurance premium equals the original aggregate mean.
--
--   **Mathematical statement**
--
--   $$
--   L_B(d)+\Pi_B(d)=\mu_B
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossLimitedMean
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean

namespace ActuarialValuation

theorem discreteStopLossLimitedMean_bridge
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossLimitedMean w bound deductible +
    discreteStopLossPremium w bound deductible =
      discreteStopLossAggregateMean w bound := by sorry

end ActuarialValuation
