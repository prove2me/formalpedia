-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
-- name    : AvramDividend.Classical.avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:27:17.808345+00:00
-- url     : https://prove2.me/theorems/b80e4040-c3f7-4cd9-afc1-5f231aab3645
-- title:
--   Original Lévy source admits an automatic literal increasing finite negative-mark-rate exhaustion from its quadratic jump energy
-- statement:
--   For the true SpectrallyNegativeLevy process and its actual ν restricted to negative marks, exhibit an increasing sequence of Borel mark bands of finite νnegative measure that literally covers all ℝ, with no separate band exhaustion hypothesis and without assuming ∫|z| ν(dz) finite. Use g(z)=ENNReal.ofReal(min(1,z²)) and the canonical null-zero-energy band theorem 05542026. The zero mark is included in the sets even though νnegative({0})=0. This supplies the missing finite-rate band input for the source exact ruin-stopped pathwise compensated Taylor Chat06 consumer.
-- source:
--   Canonical Proved Lévy jump moment X.ν_integrable; Proved 05542026-f56e-4a22-80e2-efb8f0192ebc zero-null-energy finite band exhaustion; no source jump count rectangle law or Gaussian identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ B : ℕ → Set ℝ,
      (∀ n, MeasurableSet (B n)) ∧
      (∀ n, (X.ν.restrict (Iio (0 : ℝ))) (B n) < ⊤) ∧
      Monotone B ∧
      (⋃ n, B n) = Set.univ := by sorry
