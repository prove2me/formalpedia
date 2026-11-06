-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_square_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:24:08.024945+00:00
-- url     : https://prove2.me/theorems/50312326-0cf3-4631-aed2-a848ba3ce0a5
-- title:
--   Original negative-band jump count at a bounded random clock has a quadratic budget
-- statement:
--   For the actual sample paths of a spectrally negative Lévy process, the number of negative-band jumps up to any measurable random time bounded by T has an integrable square and second moment at most r+r², where r=Tν(B). The original fixed-horizon first and factorial moments control it by pathwise inclusion.
-- source:
--   Avram original source; public exact finite negative-band marked-time finiteness and count identification, first moment and factorial moment (3d8bb7f8, c1e09ada, 0a13392f).

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_square_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by sorry
