-- Prove2me | Theorems.Thm_ActuarialValuation_pvTerm_after_expiry
-- name    : ActuarialValuation.pvTerm_after_expiry
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:42.530987+00:00
-- url     : https://prove2.me/theorems/11a51b37-5fda-424d-8352-704ae100934e
-- title:
--   Finite random present values of insurance benefits and premium streams: pvTerm_after_expiry
-- statement:
--   Term benefits vanish when the policyholder dies on or after the end of the term, with death at the exact term boundary excluded.
--
--   Mathematical relation:
--
--   $$
--   pvTerm\_after\_expiry
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvTermBenefit

namespace ActuarialValuation

theorem pvTerm_after_expiry (benefit discount : ℕ → ℝ) (term k : ℕ) (h : term ≤ k) : pvTermBenefit benefit discount term k = 0 := by sorry

end ActuarialValuation
