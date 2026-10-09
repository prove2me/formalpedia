-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskStrictMass_above
-- name    : ActuarialValuation.tailRiskStrictMass_above
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:54:56.153731+00:00
-- url     : https://prove2.me/theorems/a15b0ab7-bf81-4826-960a-78781bc72394
-- title:
--   Strict tail vanishes beyond the finite loss support
-- statement:
--   No amount in the bounded grid can exceed a quantile at or above the maximum loss. The strict tail therefore vanishes, without needing probability normalisation or positivity.
--
--   **Mathematical statement**
--
--   $$
--   q\ge B\Rightarrow T_B(q)=0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskStrictMass_above
  (w : ℕ → ℝ) (bound q : ℕ) (h : bound ≤ q) :
  tailRiskStrictMass w bound q = 0 := by sorry

end ActuarialValuation
