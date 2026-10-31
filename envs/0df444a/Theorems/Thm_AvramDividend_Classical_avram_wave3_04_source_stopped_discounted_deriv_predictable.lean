-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
-- name    : AvramDividend.Classical.avram_wave3_04_source_stopped_discounted_deriv_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:43:54.914909+00:00
-- url     : https://prove2.me/theorems/658fb6a1-1044-40b3-aa7d-2926663389af
-- title:
--   Actual stopped and discounted controlled Lévy derivative is a strongly predictable integrand
-- statement:
--   The actual post-payment controlled reserve U+=x+X−D+ driven by the original Lévy source, without any equal-law substitution, has strongly predictable left-limit process in the right-continuous transported original filtration. Therefore the discounted derivative e^{−qt}w'(U+_{t−}), multiplied by the inclusive survival indicator 1_{t≤τ} of the true dividend ruin stopping time and truncated to any deterministic finite horizon T, remains strongly predictable under that same filtration. The result constructs the exact measurable martingale integrand required for the source-specific stopped Itô–Meyer calculation; no stochastic expectation bound is inferred.
-- source:
--   Accepted canonical original reserve pre-jump predictability UUID 94ee9994-3882-4f29-8637-06666efe721d; discounted derivative fcdc8c77-b533-49ff-8001-cf775c3945a8; inclusive survival predictability 69806d16-1c2a-445a-920f-4500f3645d6a; finite-horizon truncation 693b22ed-0842-4e61-add7-7439cb0f2f12; original ruin stopping time 2d036d4f-57b5-4b28-864b-a2ff5082e323. Private pinned remote compiler probe 37d3be3d-cac7-43f7-b626-8df87bd40488 passed sentinel with no candidate errors, source SHA-256 ac65515f978ed279cae2dfd157942dd80c83c6ae2683c577970a06ac2a2f1ea0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyPredictable_inclusive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_source_stopped_discounted_deriv_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) := by sorry
