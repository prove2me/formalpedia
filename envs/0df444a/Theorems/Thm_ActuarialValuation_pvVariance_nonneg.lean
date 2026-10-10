-- Prove2me | Theorems.Thm_ActuarialValuation_pvVariance_nonneg
-- name    : ActuarialValuation.pvVariance_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:11.808457+00:00
-- url     : https://prove2.me/theorems/8f8a1908-f4c3-4a03-a534-624905fead78
-- title:
--   Equivalence premiums and loss variance: pvVariance_nonneg
-- statement:
--   Weighted second-moment variance is nonnegative for an actual finite probability distribution, requiring Jensen or weighted Cauchy-Schwarz rather than mere cancellation.
--
--   Mathematical relation:
--
--   $$
--   pvVariance\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvVariance

namespace ActuarialValuation

theorem pvVariance_nonneg {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i : Fin n, p i) = 1) : 0 ≤ pvVariance p loss := by sorry

end ActuarialValuation
