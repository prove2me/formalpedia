-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossTail_above_bound
-- name    : ActuarialValuation.discreteStopLossTail_above_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:36:00.993971+00:00
-- url     : https://prove2.me/theorems/f8b56fba-3319-437d-a466-d88fd522a35d
-- title:
--   No aggregate loss exceeds a deductible at the maximum
-- statement:
--   The strict tail event s>d is empty when d is at or above the loss support's maximum bound. The finite sum therefore has no nonzero terms, which is a useful boundary condition for backward computation of premiums.
--
--   **Mathematical statement**
--
--   $$
--   d\ge B\Longrightarrow T_B(d)=0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossTail_above_bound
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (h : bound ≤ deductible) :
  discreteStopLossTail w bound deductible = 0 := by sorry

end ActuarialValuation
