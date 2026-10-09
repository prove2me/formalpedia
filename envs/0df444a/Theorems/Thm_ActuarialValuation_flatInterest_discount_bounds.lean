-- Prove2me | Theorems.Thm_ActuarialValuation_flatInterest_discount_bounds
-- name    : ActuarialValuation.flatInterest_discount_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:39:30.453093+00:00
-- url     : https://prove2.me/theorems/6bb32538-ca77-40f1-99d4-2785fdeb06c1
-- title:
--   Flat interest discount bounds
-- statement:
--   Records that a positive flat effective rate gives a discount factor strictly between zero and one.
--
--   **Mathematical statement**
--
--   $$
--   i>0\implies 0<\frac{1}{1+i}<1
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem flatInterest_discount_bounds (i : ℝ) (hi : 0 < i)
    :
    0 < (1 / (1 + i) : ℝ) ∧ (1 / (1 + i) : ℝ) < 1 := by sorry

end ActuarialValuation
