-- Prove2me | Theorems.Thm_ActuarialValuation_pvLoading_recover
-- name    : ActuarialValuation.pvLoading_recover
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:23.144073+00:00
-- url     : https://prove2.me/theorems/e21cf7c2-76aa-4e49-a3db-9074bcbaedac
-- title:
--   Equivalence premiums and loss variance: pvLoading_recover
-- statement:
--   A loaded premium minus its equivalence rate yields exactly the specified loading.
--
--   Mathematical relation:
--
--   $$
--   pvLoading\_recover
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoading
import Definitions.Def_actuarial_pvLoadedPremium

namespace ActuarialValuation

theorem pvLoading_recover (equivalence loading : ℝ) : pvLoading (pvLoadedPremium equivalence loading) equivalence = loading := by sorry

end ActuarialValuation
