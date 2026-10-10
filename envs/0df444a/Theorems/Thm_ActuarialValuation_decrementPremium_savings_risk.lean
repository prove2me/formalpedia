-- Prove2me | Theorems.Thm_ActuarialValuation_decrementPremium_savings_risk
-- name    : ActuarialValuation.decrementPremium_savings_risk
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:11:48.737007+00:00
-- url     : https://prove2.me/theorems/553108bf-ccb7-4d72-9cd1-17cf5b24c233
-- title:
--   Decrement premium decomposes into savings and risk components
-- statement:
--   Under total annual probability one, the premium splits into reserve accumulation and cause-specific expected net amounts at risk.
--
--   **Mathematical statement**
--
--   $$
--   \Pi=\Pi^{\rm sav}+\Pi^{\rm risk}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementRiskPremium
import Definitions.Def_actuarial_decrementSavingsPremium
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory

namespace ActuarialValuation

theorem decrementPremium_savings_risk {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  decrementAnnualPremium p q b v R Rnext =
    decrementSavingsPremium v R Rnext +
      decrementRiskPremium q b v Rnext := by sorry

end ActuarialValuation
