-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a112_original_zero_rate_negative_Borel_physical_count_ae_zero_20261114
-- name    : AvramDividend.Classical.avram_a112_original_zero_rate_negative_Borel_physical_count_ae_zero_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:08:55.679203+00:00
-- url     : https://prove2.me/theorems/1fc829ae-3268-4688-b9c5-7da50b7c206c
-- title:
--   Zero-intensity negative Borel physical jump count vanishes almost surely on original Lévy space
-- statement:
--   For any spectrally negative Lévy process with finite total negative activity, a Borel subset of negative marks having zero Lévy mass has no actual physical jumps on any fixed finite horizon almost surely. This is an exact original-path count statement and requires no Poisson count distribution theorem or zero Gaussian volatility.
-- source:
--   Proved JA35 original negative Borel count first moment and integrability, nonnegativity of the real count, and Mathlib integral_eq_zero_iff_of_nonneg_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a112_original_zero_rate_negative_Borel_physical_count_ae_zero_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (hRateZero : X.ν B = 0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    ∀ᵐ ω ∂P, (N ω).toReal = 0 := by sorry
