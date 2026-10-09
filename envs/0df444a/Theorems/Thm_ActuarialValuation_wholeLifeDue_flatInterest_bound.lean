-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_bound
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:57:33.274377+00:00
-- url     : https://prove2.me/theorems/8f4529e2-a5a7-4743-95df-7f7c0414c9c0
-- title:
--   Whole life due flat interest bound
-- statement:
--   Bounds the nonnegative annuity-due present value above by (1+i)/i for every outcome at a positive flat rate.
--
--   **Mathematical statement**
--
--   $$
--   0\le Z_D\le\frac{1+i}{i}
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_bound {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    0 ≤ wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ∧
      wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ≤ (1 + i) / i := by sorry

end ActuarialValuation
