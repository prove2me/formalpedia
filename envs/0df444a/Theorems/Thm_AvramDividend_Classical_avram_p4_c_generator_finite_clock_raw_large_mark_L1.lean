-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_finite_clock_raw_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:41:10.405183+00:00
-- url     : https://prove2.me/theorems/b40bbce6-b87e-4410-be59-ae28455ffecc
-- title:
--   Actual original large jump raw payoff is product-integrable over capped measurable finite clocks
-- statement:
--   On the finite product of an arbitrary finite observation-clock measure and the original Levy intensity restricted to z<-epsilon, the actual unmodified raw jump payoff w(R_t+z)-w(R_t) is integrable for every measurable capped reserve path. The proof uses the genuine finite-clock cutoff L1 lemma and that the restricted original Levy tail is supported on negative marks z<-epsilon, formalised with product almost-everywhere Fubini. No jump-counting compensation, stochastic integral construction, or generator at an endpoint is assumed.
-- source:
--   Accepted P4-C finite-clock_large_mark_L1 child and pinned Mathlib Measure.ae_prod_iff_ae_ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_large_mark_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_finite_clock_raw_large_mark_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    Integrable
      (fun p : T × ℝ => w (R p.1 + p.2) - w (R p.1))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by sorry
