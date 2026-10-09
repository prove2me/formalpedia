-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_tail_sum
-- name    : ActuarialValuation.discreteStopLossPremium_tail_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:48:52.711974+00:00
-- url     : https://prove2.me/theorems/22a719bd-a166-4892-b411-1cd3b92e7312
-- title:
--   Stop-loss premium equals a finite sum of strict survival tails
-- statement:
--   An excess payment of integer size s-d consists of one unit for every crossed attachment level j=d,...,s-1. Swapping the two finite sums expresses the pure premium as the total strict-loss tail across all remaining covered attachment levels.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(d)=\sum_{j=d}^{B}T_B(j)
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossTail

namespace ActuarialValuation

theorem discreteStopLossPremium_tail_sum
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossPremium w bound deductible =
    ∑ j ∈ Finset.range (bound + 1),
      if deductible ≤ j then discreteStopLossTail w bound j else 0 := by sorry

end ActuarialValuation
