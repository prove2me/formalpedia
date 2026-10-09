-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_nonneg
-- name    : ActuarialValuation.discreteStopLossPremium_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:36:35.255442+00:00
-- url     : https://prove2.me/theorems/b1b0b8b2-f301-4d97-8133-d444428c08ef
-- title:
--   A nonnegative aggregate distribution yields nonnegative stop-loss premium
-- statement:
--   Every realised stop-loss payout is a nonnegative integer. Nonnegative probability masses make all weighted claim payments nonnegative and hence their finite sum, the pure stop-loss premium, cannot be negative.
--
--   **Mathematical statement**
--
--   $$
--   w_s\ge0\Longrightarrow\Pi_B(d)\ge0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium

namespace ActuarialValuation

theorem discreteStopLossPremium_nonneg
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ discreteStopLossPremium w bound deductible := by sorry

end ActuarialValuation
