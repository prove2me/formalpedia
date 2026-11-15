-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
-- name    : AvramDividend.Classical.avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:52:09.830255+00:00
-- url     : https://prove2.me/theorems/f2242dea-df95-4045-b6f1-64e0d3aeff64
-- title:
--   Original finite-cap BV HJB closed-cap discounted drift and negative-mark compensator time-budget
-- statement:
--   For the original Standing BV process with finite negative-mark activity and a finite positive reserve cap, integrate the closed-cap HJB generator inequality at C against exp(-qt) over any deterministic horizon T>=0, keeping the ORIGINAL negative-mark compensator integral and full-T discounted terminal w(C). This gives a precise sharp bound on cash paid at the upper reserve cap and supplies the cap-contact Stieltjes case. Use existing Proved cap boundary HJB 32ce498d and discounted integral identity 5ce1f298.
-- source:
--   32ce498d Proved and 5ce1f298 Proved, original cap-contact Stieltjes BV-B source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T) :
    X.drift * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) * w C.toReal ≤
    w C.toReal -
      (∫ z in Iio (0 : ℝ), w (C.toReal + z) - w C.toReal ∂X.ν) *
        (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) := by sorry
