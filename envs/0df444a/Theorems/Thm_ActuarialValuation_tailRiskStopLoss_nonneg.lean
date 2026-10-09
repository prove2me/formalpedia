-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskStopLoss_nonneg
-- name    : ActuarialValuation.tailRiskStopLoss_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:55:34.602209+00:00
-- url     : https://prove2.me/theorems/3129a0d7-ee58-4077-a5c3-a16a9c36f450
-- title:
--   Positive probability weights give nonnegative quantile excess premium
-- statement:
--   Natural-number excess payments are never negative. Weighting them by nonnegative claim probabilities preserves nonnegativity term by term in the finite stop-loss sum.
--
--   **Mathematical statement**
--
--   $$
--   w_s\ge0\Rightarrow\Pi_B(q)\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskStopLoss_nonneg
  (w : ℕ → ℝ) (bound q : ℕ) (hw : ∀ s, 0 ≤ w s) :
  0 ≤ tailRiskStopLoss w bound q := by sorry

end ActuarialValuation
