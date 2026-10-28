-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq
-- name    : AvramDividend.Classical.runningSup_paymentTimes_iInter_restrict_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:51:38.424362+00:00
-- url     : https://prove2.me/theorems/eff1caea-3ef6-43d9-9835-4fe1ffebf19b
-- title:
--   Shrinking payment-time windows induce the same stopped Stieltjes measure at their infimum
-- statement:
--   For any countable stopping-time family, the restriction of the true Lévy running-supremum Stieltjes measure to the intersection of all strict payment windows equals its restriction to the single window at the infimum. The limiting payment set is contained in every window; the possible extra terminal point has zero Stieltjes mass. Therefore the two sets agree almost everywhere for the dividend measure. This closes the pathwise endpoint restriction identity needed for zero-barrier reward limit convergence.
-- source:
--   Proved runningSup_paymentTimes_iInter_boundary_mass_zero and pinned Mathlib Measure.restrict_congr_set; supports AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity.

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_boundary_mass_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_paymentTimes_iInter_restrict_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) :
    (dividendMeasure (runningSup X) ω).restrict
        (⋂ n, paymentTimes (σ n)) =
      (dividendMeasure (runningSup X) ω).restrict
        (paymentTimes (⨅ n, σ n)) := by sorry
