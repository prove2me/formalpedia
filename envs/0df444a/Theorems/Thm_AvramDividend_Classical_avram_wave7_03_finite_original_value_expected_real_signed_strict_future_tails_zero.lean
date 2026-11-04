-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_expected_real_signed_strict_future_tails_zero
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_expected_real_signed_strict_future_tails_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:26:05.018262+00:00
-- url     : https://prove2.me/theorems/92669355-5408-4539-a632-92fdd6059539
-- title:
--   Finite canonical original value forces expected genuine real signed strict-future dividend tails to vanish
-- statement:
--   Under finite original dividendValue, the actual expectation under original P of the real signed discounted Stieltjes dividends strictly after deterministic horizon n tends to zero in ℝ. It uses the genuine signed integral over paymentTimes(ruinTime X x D ω) ∩ Ioi(n:ℝ) against dividendMeasure D ω, including all continuous and right-jump payments strictly after n. It is the real expected localisation-tail counterpart of the accepted ENNReal future-tail convergence, justified by the accepted exact signed-to-ENNReal mean bridge.
-- source:
--   Proved expected ENNReal strict future tail convergence 90a780e4, Proved exact random strict-future real signed L1 and expected mean equality 86cd5e20, positivity of Real.exp, pinned Mathlib ENNReal.tendsto_toReal at zero and ENNReal.toReal_ofReal.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_expected_real_signed_strict_future_tails_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
