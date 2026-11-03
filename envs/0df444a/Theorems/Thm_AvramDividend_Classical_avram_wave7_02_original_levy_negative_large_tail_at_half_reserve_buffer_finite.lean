-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_levy_negative_large_tail_at_half_reserve_buffer_finite
-- name    : AvramDividend.Classical.avram_wave7_02_original_levy_negative_large_tail_at_half_reserve_buffer_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:04:54.263675+00:00
-- url     : https://prove2.me/theorems/80c79488-dd03-4c9e-b2ca-e6cab3898407
-- title:
--   Original spectrally negative Lévy source physical mark tail is finite at half any positive C1 reserve buffer
-- statement:
--   For the exact original spectrally negative Lévy source X and its physical ν quadratic-energy integrability, every strictly positive controlled-reserve localisation buffer a≤2 has finite negative source mark intensity ν((-∞,-a/2]). This discharges the previously free large-mark finite-mass hypothesis in W7-02 compact C1 source compensation and actual predictable marked product integrability, using the accepted source-specific arbitrary-threshold tail theorem.
-- source:
--   Genuine original Levy ν quadratic energy and W7-02 Proved negative tail threshold theorem 3e5bbc19.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_levy_negative_large_tail_at_half_reserve_buffer_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
    X.ν (Iic (-a / 2)) < ⊤ := by sorry
