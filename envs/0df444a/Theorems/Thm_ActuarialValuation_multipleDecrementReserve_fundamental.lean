-- Prove2me | Theorems.Thm_ActuarialValuation_multipleDecrementReserve_fundamental
-- name    : ActuarialValuation.multipleDecrementReserve_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:15:41.260346+00:00
-- url     : https://prove2.me/theorems/bc9fe8a5-ca9c-4fdd-8bd8-da51585355fb
-- title:
--   Fundamental multiple-decrement reserve and risk premium theorem
-- statement:
--   Combines annual reserve balance and decomposition of the required premium into savings and risk amounts.
--
--   **Mathematical statement**
--
--   $$
--   R+\Pi=v(pR_++\sum_jq_jb_j),\qquad \Pi=\Pi^{\rm sav}+\Pi^{\rm risk}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementExpectedBenefit
import Definitions.Def_actuarial_decrementRiskPremium
import Definitions.Def_actuarial_decrementSavingsPremium
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory

namespace ActuarialValuation

theorem multipleDecrementReserve_fundamental {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ) (h : isAnnualDecrementLaw p q)
  :
  (R + decrementAnnualPremium p q b v R Rnext =
    v * (p * Rnext + decrementExpectedBenefit q b))
  ∧ (decrementAnnualPremium p q b v R Rnext =
    decrementSavingsPremium v R Rnext +
      decrementRiskPremium q b v Rnext) := by sorry

end ActuarialValuation
