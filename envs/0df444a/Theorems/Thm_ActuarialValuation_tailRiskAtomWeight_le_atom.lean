-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskAtomWeight_le_atom
-- name    : ActuarialValuation.tailRiskAtomWeight_le_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:09:54.232703+00:00
-- url     : https://prove2.me/theorems/ba08ffac-8308-4c36-9fde-f7b70f197ef6
-- title:
--   Selected worst-tail fraction cannot exceed quantile-point mass
-- statement:
--   The quantile condition ensures enough probability is available at losses exactly equal to q to fill the requested worst-tail percentage after including all larger losses. The selected fraction of the quantile-point mass is therefore at most w(q).
--
--   **Mathematical statement**
--
--   $$
--   1-\alpha\le T_B(q)+w_q\Rightarrow a_q\le w_q
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskAtomWeight_le_atom
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hquantile : 1 - alpha ≤ tailRiskStrictMass w bound q + w q) :
  tailRiskAtomWeight w bound q alpha ≤ w q := by sorry

end ActuarialValuation
