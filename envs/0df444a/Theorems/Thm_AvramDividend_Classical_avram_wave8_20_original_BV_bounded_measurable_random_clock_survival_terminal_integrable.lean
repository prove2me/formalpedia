-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:03.41331+00:00
-- url     : https://prove2.me/theorems/8949220f-3a95-4bd0-8ddb-bfdbbefbf3df
-- title:
--   Source BV strict-survival terminal integrability for any bounded measurable random clock, without stopping assumption
-- statement:
--   For the original spectrally negative bounded-variation Levy process and admissible capped dividend strategy, any measurable nonnegative random clock bounded by a finite physical horizon has integrable discounted nonnegative post-rightpayment HJB candidate on strict survival. No stopping-time predicate, optional sampling or desired supermartingale inequality is assumed, strengthening the earlier W8-20 stopping-time L1 lemma.
-- source:
--   Original BV stochastic verification support for W8-04. The accepted original postpayment reserve joint measurability gives source terminal measurability at any measurable random time. The accepted wave8-20 random-clock pathwise uniform envelope gives deterministic L1 domination, via the original Standing probability measure. The exact strict survival, real exponential and rightLimit D remain unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ)
    (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by sorry
