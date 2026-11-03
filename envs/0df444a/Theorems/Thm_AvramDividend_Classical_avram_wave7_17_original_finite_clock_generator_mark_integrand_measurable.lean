-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_generator_mark_integrand_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_finite_clock_generator_mark_integrand_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:54:55.864249+00:00
-- url     : https://prove2.me/theorems/71f519c2-3a07-4a3e-8b41-4d428f4a987d
-- title:
--   Original finite-clock predictable negative-source generator integrand is Borel measurable in physical time × Ω × real Lévy marks
-- statement:
--   For the original Lévy process X, its actual post-dividend strict-left-limit reserve Y, and the original generator HJB candidate w continuous on nonnegative reserves and zero on negative reserves, the complete source generator integrand w(Y+z)-w(Y)-deriv w(Y) z 1_{(-1,1)}(z), zeroed outside a finite deterministic physical clock, is jointly measurable on original Borel physical time × sample Ω × real jump-mark space. The derivative is Borel measurable and no alternate Poisson process is introduced. This supplies the compensated-generator marked integrand measurability needed by stopped BV HJB verification, but is not an intrinsic source-jump compensation identity or integrability bound.
-- source:
--   Actual source generator kernel from original SpectrallyNegativeLevy definition and BV drift-compensation formula, Avram-Palmowski-Pistorius (2007) Proposition 4(i). Uses Proved global Borel candidate 30325a04, Proved original strongly predictable finite-clock reserve d8a9025e, and pinned Mathlib measurable_deriv.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_finite_clock_generator_mark_integrand_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (T : ℝ≥0) :
    Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      if p.1.1 ≤ T then
        SpectrallyNegativeLevy.generatorIntegrand w
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) p.2
      else 0) := by sorry
