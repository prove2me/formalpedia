-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualPremium_zero_causes
-- name    : ActuarialValuation.decrementAnnualPremium_zero_causes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:32:45.86873+00:00
-- url     : https://prove2.me/theorems/a62f28bd-30eb-4a9a-80dd-59081c62ce28
-- title:
--   Annual premium in the no-decrement scenario
-- statement:
--   With certain survival and no causes of decrement, the premium only adjusts the reserve.
--
--   **Mathematical statement**
--
--   $$
--   p=1,q=0\Rightarrow\Pi=\Pi^{\rm sav}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementSavingsPremium
open MeasureTheory

namespace ActuarialValuation

theorem decrementAnnualPremium_zero_causes {J : Type*} [Fintype J] (p : ℝ) (b : J → ℝ) (v R Rnext : ℝ)
  (hp : p = 1)
  :
  decrementAnnualPremium p (fun _ => 0) b v R Rnext =
    decrementSavingsPremium v R Rnext := by sorry

end ActuarialValuation
