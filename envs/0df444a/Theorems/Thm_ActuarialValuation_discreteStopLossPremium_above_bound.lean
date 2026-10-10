-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_above_bound
-- name    : ActuarialValuation.discreteStopLossPremium_above_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:35:19.041993+00:00
-- url     : https://prove2.me/theorems/0ef22546-caee-44df-b5ce-e349fed0969d
-- title:
--   Attachment at or above maximum loss gives zero premium
-- statement:
--   When the deductible is no smaller than the greatest possible aggregate loss in the bounded model, no realised claim triggers reinsurance. Every positive-part term vanishes, irrespective of the shape of the probability weights.
--
--   **Mathematical statement**
--
--   $$
--   d\ge B\Longrightarrow\Pi_B(d)=0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium

namespace ActuarialValuation

theorem discreteStopLossPremium_above_bound
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (h : bound ≤ deductible) :
  discreteStopLossPremium w bound deductible = 0 := by sorry

end ActuarialValuation
