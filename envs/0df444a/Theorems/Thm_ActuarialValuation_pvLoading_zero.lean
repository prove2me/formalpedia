-- Prove2me | Theorems.Thm_ActuarialValuation_pvLoading_zero
-- name    : ActuarialValuation.pvLoading_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:09.303237+00:00
-- url     : https://prove2.me/theorems/d23279c4-32fa-4601-b1e6-a146f1b3a19b
-- title:
--   Equivalence premiums and loss variance: pvLoading_zero
-- statement:
--   Charging the equivalence rate gives a zero premium loading.
--
--   Mathematical relation:
--
--   $$
--   pvLoading\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoading

namespace ActuarialValuation

theorem pvLoading_zero (equivalence : ℝ) : pvLoading equivalence equivalence = 0 := by sorry

end ActuarialValuation
