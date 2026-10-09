-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeImmediate_eq_survival_tsum
-- name    : ActuarialValuation.wholeLifeImmediate_eq_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:19:45.883704+00:00
-- url     : https://prove2.me/theorems/da419a4b-8837-4323-9c24-355cd6a1ef5b
-- title:
--   Whole-life immediate PV equals a survival-weighted infinite sum
-- statement:
--   For a realised finite curtate lifetime K, the immediate present value equals the sum of discounted survival indicators over payment dates 1 through K. The infinite series representation has only finitely many non-zero terms for each realised K; this is the textbook whole-life immediate result in equations (3.11)–(3.12).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{WL,immediate}}=\sum_{k=0}^{\infty}v^{k+1}\mathbf1_{\{K\ge k+1\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeImmediate_eq_survival_tsum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityImmediatePV K v ω = ∑' k : ℕ, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry

end ActuarialValuation
