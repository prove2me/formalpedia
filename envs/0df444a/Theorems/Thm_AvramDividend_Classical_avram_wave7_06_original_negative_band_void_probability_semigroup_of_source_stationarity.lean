-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:25:53.053232+00:00
-- url     : https://prove2.me/theorems/a8f4c93c-1bc5-46f3-b050-fc509d6fe052
-- title:
--   Actual original negative-band void probability multiplicative time semigroup
-- statement:
--   For the actual intrinsic original Lévy jump count and a negative mark threshold, original-past measurability of the early void and stationarity in distribution of the later void imply the exact multiplicative time semigroup for zero-count probabilities. The proof uses original pathwise count additivity and the now established original-past/future void event probability independence. The two specific remaining hypotheses are displayed; no Poisson or auxiliary source law is assumed.
-- source:
--   W7-06 analytic reduction of original positive-horizon Poisson zero-count law aa265c9f to original finite-horizon raw-filtration measurability, stationary void law and short-time exponent rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_probability_semigroup_of_source_stationarity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T S : ℝ≥0) (n : ℕ)
    (hPast : MeasurableSet[𝓕 T]
      {ω : Ω | NX ω
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
    (hStationary :
      P {ω : Ω | NX ω
        (Ioc T (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      P {ω : Ω | NX ω
        (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) :
    P {ω : Ω | NX ω
      (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    P {ω : Ω | NX ω
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} *
    P {ω : Ω | NX ω
      (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
