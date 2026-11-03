-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:51:13.343203+00:00
-- url     : https://prove2.me/theorems/e428a145-fea9-4966-8fc4-f7e4d159f857
-- title:
--   Actual source marked negative-jump HJB value increment is jointly measurable on finite physical time × original P × Lévy marks
-- statement:
--   The exact original prepayment reserve left-limit and negative source jump-mark value increment w(Y+z)-w(Y), zeroed after an arbitrary finite physical horizon, is jointly Borel measurable on (time × original Ω) × real mark space, with the original Lévy source and original dividend strategy unchanged. Handles the candidate's possible jump discontinuity at reserve zero using continuousOn Ici0 and zero extension for negative reserves. This is a finite-clock measurable-integrand prerequisite for the actual source marked jump compensator and stopped HJB expectation, not a compensation identity.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), actual controlled Lévy negative-source-jump generator. Uses Proved 30325a04 Borel candidate and finite-clock predictable reserve joint measurable helper d8a9025e, once its proof is Proved. Original Ω,P,X,𝓕,D, and ν mark variable are retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
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
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)
      else 0) := by sorry
