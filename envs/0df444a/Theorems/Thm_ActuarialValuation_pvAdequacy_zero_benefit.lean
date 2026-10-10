-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_zero_benefit
-- name    : ActuarialValuation.pvAdequacy_zero_benefit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:13.097982+00:00
-- url     : https://prove2.me/theorems/c4e18bb7-291c-4777-bc1c-e06161aba493
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_zero_benefit
-- statement:
--   Nonnegative premium receipts always cover a zero insurance benefit in every scenario.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_zero\_benefit
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

namespace ActuarialValuation

theorem pvAdequacy_zero_benefit {n : ℕ} (p annuity : Fin n → ℝ) (premium : ℝ) (hprem : 0 ≤ premium) (ha : ∀ i, 0 ≤ annuity i) : pvAdequacy p (fun _ => 0) annuity premium = ∑ i : Fin n, p i := by sorry

end ActuarialValuation
