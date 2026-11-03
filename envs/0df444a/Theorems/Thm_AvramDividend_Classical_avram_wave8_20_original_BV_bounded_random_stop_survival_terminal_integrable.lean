-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:03:01.45342+00:00
-- url     : https://prove2.me/theorems/b438eaf6-f345-46cb-80bd-875ff9e9ca3f
-- title:
--   Original stopped BV strict-survival terminal integrable at every bounded right-continuous stopping clock
-- statement:
--   For the original Standing BV source and admissible dividend strategy, every bounded genuine right-continuous filtration stopping clock has an integrable strictly surviving discounted positive-part postrightpayment terminal. Original source Borel measurability at the stopped reserve is combined with one shared almost-sure BV physical drift ceiling; the result neither assumes the desired stochastic inequality nor a finite cap.
-- source:
--   Exact original Avram Proposition 4(i) random localisation: uniform pathwise BV clock domination (W8-20 helper 2563fd4a) and genuine right-continuous-filtration stopped postpayment reserve measurability (proved 4238f416), original ruin measurability, and Borel HJB test. No stopped generator supermartingale inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by sorry
