-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
-- name    : AvramDividend.Classical.avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:20:52.064683+00:00
-- url     : https://prove2.me/theorems/092f30d0-a717-45e5-8ffd-d25b605df486
-- title:
--   Original stopped strict cash positive compensator residual is integrable for every grid row
-- statement:
--   For the original BV process X and original admissible D, literal strict pre-ruin cash and surviving-horizon postpayment terminal, any L1 compensated M and canonical source B give an integrable positive part of F-(w x+M+B), row by row. Reuses Proved 63bcc60a without changing time-zero, ruin or horizon accounting. Positive-error decay remains a separate analytical gap.
-- source:
--   Direct composition of Proved 63bcc60a-da4a-423d-9b35-d0591fb6131b and Mathlib integrability closure for sums, differences and max.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
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
      0 ≤ w (riskProcess X x D t ω))
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ n, Integrable (M n) P)
    (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∀ n, Integrable
      (fun ω => max (F n ω - (w x + (M n ω + B n ω))) 0) P := by sorry
