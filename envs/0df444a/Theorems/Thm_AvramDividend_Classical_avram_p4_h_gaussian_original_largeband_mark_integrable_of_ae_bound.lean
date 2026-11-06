-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:28:43.419668+00:00
-- url     : https://prove2.me/theorems/27b07e57-79d5-4806-a458-bb0b2504b824
-- title:
--   Original large-jump signed mark is pathwise integrable from finite source intensity and verifiable tail bound
-- statement:
--   For the original Levy sample path, use the already Proved finite large-negative-band intrinsic count to establish a finite measure and obtain pathwise IntegrableOn for its signed marks from an explicit almost-everywhere mark bound under that precise original restricted measure. The remaining premise is a finite-mark bound on actual X.X jumps, recoverable from the Proved finite large jump-time support; no additional process or stochastic law is assumed.
-- source:
--   Proved original separated negative-band intrinsic count finite on each path 3537a106; pinned Mathlib isFiniteMeasure_restrict, measurable_snd.aestronglyMeasurable, Integrable.of_bound.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    ∀ C : ℝ, (∀ᵐ p ∂(N.restrict E), ‖p.2‖ ≤ C) →
      IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N := by sorry
