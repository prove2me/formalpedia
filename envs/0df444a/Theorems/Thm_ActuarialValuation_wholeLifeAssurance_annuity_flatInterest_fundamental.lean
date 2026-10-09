-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeAssurance_annuity_flatInterest_fundamental
-- name    : ActuarialValuation.wholeLifeAssurance_annuity_flatInterest_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:02:53.190088+00:00
-- url     : https://prove2.me/theorems/8186ee11-83e1-4820-a963-4a2af387caf9
-- title:
--   Whole life assurance annuity flat interest fundamental
-- statement:
--   Collects the pointwise relation, EPV relation, variance scaling, and unit identity as the capstone statement for positive flat interest.
--
--   **Mathematical statement**
--
--   $$
--   \begin{aligned}Z_D&=\frac{1+i}{i}(1-Z_A)\\\mathbb E[Z_D]&=\frac{1+i}{i}(1-\mathbb E[Z_A])\\\operatorname{Var}(Z_D)&=\left(\frac{1+i}{i}\right)^2\operatorname{Var}(Z_A)\end{aligned}
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeAssurance_annuity_flatInterest_fundamental {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    (∀ ω, wholeLifeAnnuityDuePV K (1 / (1 + i)) ω =
      ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω))
    ∧ ((∫ ω, wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ∂P) =
      ((1 + i) / i) *
      (1 - ∫ ω, wholeLifeAssurancePV K (1 / (1 + i)) ω ∂P))
    ∧ (ProbabilityTheory.variance
      (wholeLifeAnnuityDuePV K (1 / (1 + i))) P =
      (((1 + i) / i) ^ 2) * ProbabilityTheory.variance
      (wholeLifeAssurancePV K (1 / (1 + i))) P)
    ∧ (∀ ω, wholeLifeAssurancePV K (1 / (1 + i)) ω +
      (i / (1 + i)) * wholeLifeAnnuityDuePV K (1 / (1 + i)) ω = 1) := by sorry

end ActuarialValuation
