-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_mono
-- name    : ActuarialValuation.crExpected_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:12.435283+00:00
-- url     : https://prove2.me/theorems/4f595b07-f61c-463f-8ea2-eb923609dde5
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_mono
-- statement:
--   An almost surely larger insurer outgo has no smaller expected loss under a nonnegative probability law.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_mono
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_mono {n : ℕ} (p X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crExpected p X≤crExpected p Y := by sorry

end ActuarialValuation
