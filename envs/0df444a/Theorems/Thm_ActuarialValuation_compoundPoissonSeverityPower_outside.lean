-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_outside
-- name    : ActuarialValuation.compoundPoissonSeverityPower_outside
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:28:42.935556+00:00
-- url     : https://prove2.me/theorems/0597c5c5-1f88-4ddc-a90b-1e2c05cbb4b1
-- title:
--   Positive severities rule out more claims than aggregate units
-- statement:
--   If each claim is at least one unit, then m realised claims cannot sum to an aggregate size smaller than m. This support fact explains why mixing the count probabilities only up to m=s is exact even though a genuine Poisson claim count is unbounded.
--
--   **Mathematical statement**
--
--   $$
--   s<m,\ f(0)=0\Longrightarrow f^{*m}(s)=0
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonSeverityPower_outside
  (f : ℕ → ℝ) (m s : ℕ) (hzero : f 0 = 0) (h : s < m) :
  compoundPoissonSeverityPower f m s = 0 := by sorry

end ActuarialValuation
