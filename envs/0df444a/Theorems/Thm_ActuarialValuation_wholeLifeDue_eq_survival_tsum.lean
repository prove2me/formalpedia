-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_eq_survival_tsum
-- name    : ActuarialValuation.wholeLifeDue_eq_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:35:58.713186+00:00
-- url     : https://prove2.me/theorems/f53bf99a-08c2-47b1-9d93-3b37afc93703
-- title:
--   Whole-life due PV equals a survival-weighted infinite sum
-- statement:
--   For a realised finite curtate lifetime K, the due present value equals the sum of discounted survival indicators over payment dates 0 through K. The infinite series representation has only finitely many non-zero terms for each realised K; this is the textbook whole-life due result in equations (3.11)–(3.12).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{WL,due}}=\sum_{k=0}^{\infty}v^k\mathbf1_{\{K\ge k\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_eq_survival_tsum {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityDuePV K v ω = ∑' k : ℕ, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry

end ActuarialValuation
