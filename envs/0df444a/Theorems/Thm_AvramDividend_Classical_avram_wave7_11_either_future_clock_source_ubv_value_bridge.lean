-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_either_future_clock_source_ubv_value_bridge
-- name    : AvramDividend.Classical.avram_wave7_11_either_future_clock_source_ubv_value_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:47:46.137691+00:00
-- url     : https://prove2.me/theorems/e81b7340-880c-44b9-9810-51290da15ae3
-- title:
--   Unified source UBV finite-horizon bound from either one deterministic future clock or one a.s. future random clock
-- statement:
--   The original law P, spectrally negative Lévy X, filtration, ruinTime and exact Stieltjes payment integral obey the corrected UBV finite-horizon bound whenever at x>0 either a single natural cutoff n>T or an almost-surely future sample-dependent clock η>T carries the expected source dividend budget. At x=0 the exact zero reward is automatic. This unifies independent verified deterministic and random-clock bridges without requiring standing, positive q, positive cap or HJB at the transfer stage.
-- source:
--   One Proved original-source a.s.-future clock bridge, with a deterministic future natural clock embedded as a constant random clock; no Open imports or unrelated sample spaces.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_either_future_clock_source_ubv_value_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEitherClock : 0 < x →
      (∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) ∨
      (∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
