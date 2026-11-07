-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
-- name    : AvramDividend.Classical.avram_p3_comp8_original_canonical_strict_prefix_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:24:41.630992+00:00
-- url     : https://prove2.me/theorems/63bcc60a-da4a-423d-9b35-d0591fb6131b
-- title:
--   Original canonical strict discounted cash plus surviving terminal is L1 on each uniform inner horizon
-- statement:
--   The literal original F_n from 4044d709 is P-integrable for every n under original X BV, D admissibility and candidate w assumptions; direct reuse of Proved 605f662e and 1b35e77b, with no cash/HJB supermartingale conclusion assumed.
-- source:
--   Original 4044d709 F and Proved source cash-prefix positive Fatou and exact margin sequence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_canonical_strict_prefix_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n, Integrable (F n) P := by sorry
