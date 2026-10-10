-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossTail_increment
-- name    : ActuarialValuation.discreteStopLossTail_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:38:19.629828+00:00
-- url     : https://prove2.me/theorems/a5d5c34e-e8a2-4995-9c2b-fe07c1b84afa
-- title:
--   The strict tail decreases by the mass at the next loss unit
-- statement:
--   The difference between exceeding d and exceeding d+1 is exactly the scenario with claim amount d+1, provided that amount lies inside the finite support. Outside the covered loss grid the increment is zero.
--
--   **Mathematical statement**
--
--   $$
--   T_B(d)-T_B(d+1)=w_{d+1}\mathbf1_{\{d+1\le B\}}
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossTail_increment
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossTail w bound deductible =
    discreteStopLossTail w bound (deductible + 1) +
      (if deductible + 1 ≤ bound then w (deductible + 1) else 0) := by sorry

end ActuarialValuation
