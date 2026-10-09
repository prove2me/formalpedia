-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualPremium_balance
-- name    : ActuarialValuation.decrementAnnualPremium_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:31:14.100782+00:00
-- url     : https://prove2.me/theorems/90fb0b3f-e640-4853-b85d-ebb548d0fff7
-- title:
--   Annual premium satisfies the one-year expected reserve balance
-- statement:
--   Opening reserve and defined premium exactly finance the expected discounted following-year liability and decrement claims.
--
--   **Mathematical statement**
--
--   $$
--   R+\Pi=v(pR_++\sum_jq_jb_j)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementExpectedBenefit
open MeasureTheory

namespace ActuarialValuation

theorem decrementAnnualPremium_balance {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ)
  :
  R + decrementAnnualPremium p q b v R Rnext =
    v * (p * Rnext + decrementExpectedBenefit q b) := by sorry

end ActuarialValuation
