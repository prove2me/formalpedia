-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_cdf_unit_annuity
-- name    : ActuarialValuation.pvAdequacy_cdf_unit_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:51.858677+00:00
-- url     : https://prove2.me/theorems/1d9850cc-f480-473b-bfeb-ad9e622454e9
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_cdf_unit_annuity
-- statement:
--   When every scenario requires exactly one premium unit, solvency probability at premium P equals the actual benefit-loss CDF evaluated at P.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_cdf\_unit\_annuity
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvAdequacy_cdf_unit_annuity {n : ℕ} (p benefit : Fin n → ℝ) (premium : ℝ) : pvAdequacy p benefit (fun _ => 1) premium = pvCdf p benefit premium := by sorry

end ActuarialValuation
