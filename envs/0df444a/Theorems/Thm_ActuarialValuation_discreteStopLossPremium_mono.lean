-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPremium_mono
-- name    : ActuarialValuation.discreteStopLossPremium_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:39:03.393434+00:00
-- url     : https://prove2.me/theorems/6105cb1a-330c-4a4e-bbdf-e987441382e3
-- title:
--   Increasing stop-loss retention does not increase its premium
-- statement:
--   At every realised aggregate loss, a higher insurer attachment reduces or preserves the reinsurer's excess payment. Under nonnegative probability weights, this pathwise ordering passes through finite expectation and yields a nonincreasing premium curve.
--
--   **Mathematical statement**
--
--   $$
--   d\le e\Longrightarrow\Pi_B(e)\le\Pi_B(d)
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium

namespace ActuarialValuation

theorem discreteStopLossPremium_mono
  (w : ℕ → ℝ) (bound d e : ℕ)
  (hw : ∀ s, 0 ≤ w s) (hde : d ≤ e) :
  discreteStopLossPremium w bound e ≤
    discreteStopLossPremium w bound d := by sorry

end ActuarialValuation
