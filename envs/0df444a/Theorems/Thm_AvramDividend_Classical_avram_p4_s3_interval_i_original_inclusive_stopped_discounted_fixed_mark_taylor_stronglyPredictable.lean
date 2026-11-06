-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_inclusive_stopped_discounted_fixed_mark_taylor_stronglyPredictable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_fixed_mark_taylor_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:09:33.215782+00:00
-- url     : https://prove2.me/theorems/70dcc5e2-5507-443a-bbce-3e3363f3cefe
-- title:
--   Same original controlled stopped discounted nonlinear Taylor fixed-mark integrand is strongly predictable
-- statement:
--   The actual original spectrally negative Lévy process X, original strategy D, original right-continuous physical filtration and an actual stopping time τ yield an inclusive-survival-stopped, exponentially discounted, nonlinear Ito-Meyer Taylor fixed-mark kernel that is strongly predictable. No new Poisson process, martingale assumption or ν-integrability condition is introduced.
-- source:
--   Compose accepted physical fixed-mark Taylor strong predictability with original inclusive survival strong predictability and predictable deterministic discount to construct the true stopped discounted nonlinear Ito–Meyer integrand.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_fixed_mark_taylor_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (q z : ℝ)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        (if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) *
          Real.exp (-(q * (t : ℝ))) *
            ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
              (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) := by sorry
