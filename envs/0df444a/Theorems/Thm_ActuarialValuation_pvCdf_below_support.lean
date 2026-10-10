-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_below_support
-- name    : ActuarialValuation.pvCdf_below_support
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:45.807799+00:00
-- url     : https://prove2.me/theorems/490f7e42-c87e-477d-a3c3-0a3cc1e6e0e9
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_below_support
-- statement:
--   The loss CDF vanishes strictly below every possible realised loss.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_below\_support
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_below_support {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hmin : ∀ i, z < loss i) : pvCdf p loss z = 0 := by sorry

end ActuarialValuation
