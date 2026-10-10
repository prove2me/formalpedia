-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_loss_cdf
-- name    : ActuarialValuation.pvAdequacy_loss_cdf
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:05.996035+00:00
-- url     : https://prove2.me/theorems/5d7a0895-1d37-4b33-95ff-5252e2ecc141
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_loss_cdf
-- statement:
--   The probability that premiums are adequate is exactly the actual prospective-loss distribution evaluated at loss zero.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_loss\_cdf
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss

namespace ActuarialValuation

theorem pvAdequacy_loss_cdf {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : pvAdequacy p benefit annuity premium = pvCdf p (pvLoss benefit annuity premium) 0 := by sorry

end ActuarialValuation
