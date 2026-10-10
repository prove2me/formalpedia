-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLoss_fundamental
-- name    : ActuarialValuation.discreteStopLoss_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:52:00.258813+00:00
-- url     : https://prove2.me/theorems/b73d48d9-00cc-4e75-93c4-7582a9a56a50
-- title:
--   Exact stop-loss premium, limited-mean bridge and convex attachment curve
-- statement:
--   The capstone combines three essential finite discrete stop-loss properties: exact loss conservation between retained and ceded layers in expectation, premium computation by aggregate-loss tail probabilities and nonnegative attachment-curve curvature. All three hold for a bounded, nonnegative aggregate-claim mass model.
--
--   **Mathematical statement**
--
--   $$
--   L_B(d)+\Pi_B(d)=\mu_B,\ \Pi_B(d)=\sum_{j=d}^BT_B(j),\ \Delta^2\Pi_B(d)\ge0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossLimitedMean
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLoss_fundamental
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  (discreteStopLossLimitedMean w bound deductible +
    discreteStopLossPremium w bound deductible =
      discreteStopLossAggregateMean w bound) ∧
  (discreteStopLossPremium w bound deductible =
    ∑ j ∈ Finset.range (bound + 1),
      if deductible ≤ j then discreteStopLossTail w bound j else 0) ∧
  (discreteStopLossPremium w bound deductible +
    discreteStopLossPremium w bound (deductible + 2) ≥
      2 * discreteStopLossPremium w bound (deductible + 1)) := by sorry

end ActuarialValuation
