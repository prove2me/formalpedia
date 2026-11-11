-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise32_original_smallband_future_increment_condexp_zero
-- name    : AvramDividend.Classical.avram_anoise32_original_smallband_future_increment_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:41:08.711603+00:00
-- url     : https://prove2.me/theorems/ded68e70-ceb3-430b-9b7b-a12af5fac748
-- title:
--   Original signed small-band future increment is conditionally centred
-- statement:
--   For an original finite-activity spectrally negative Lévy process and each fixed small negative mark cut-off, the compensated sum of marks arising strictly after s and through t has conditional expectation zero given the original right-continuous filtration at s. This follows by the original Lévy marked-measure Campbell rectangle identity for signed bounded weights and the right-continuous filtration limit. It isolates the genuine future-increment calculation from the past-value measurability and conditional-expectation linearity required by avram_anoise31.
-- source:
--   Sound reduction of original signed small-band right-continuous martingale 867b4b3a. The child expresses conditional centring of the strict future compensator increment; the parent additionally requires source adaptedness and condExp subtraction. Reuse Proved 12ff9a1a weighted Campbell, 231bacab right-continuous centred marked counts, 613d1237 signed shift, and 5398685b integrability. Same Ω, P and filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise32_original_smallband_future_increment_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ u : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) ω = 0 := by sorry
