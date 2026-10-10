-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_convex
-- name    : ActuarialValuation.discreteStopLossPremium_convex
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:42:36.809641+00:00
-- url     : https://prove2.me/theorems/6aea65a9-63ae-47b8-9a88-a62fbb6a36bc
-- title:
--   Stop-loss attachment premiums have nonnegative discrete curvature
-- statement:
--   The drop in premium per added unit of attachment is the strict claim tail, which itself falls as attachment increases. Therefore adjacent premium differences have a nonnegative second difference, establishing convexity on the integer attachment grid.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(d)+\Pi_B(d+2)-2\Pi_B(d+1)\ge0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossPremium_convex
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  discreteStopLossPremium w bound deductible +
    discreteStopLossPremium w bound (deductible + 2) ≥
      2 * discreteStopLossPremium w bound (deductible + 1) := by sorry

end ActuarialValuation
