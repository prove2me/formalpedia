-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys38_original_finite_simple_negative_mark_compensation
-- name    : AvramDividend.Classical.avram_bvb_phys38_original_finite_simple_negative_mark_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:35:13.236+00:00
-- url     : https://prove2.me/theorems/e4698f5a-0aa9-4c1e-b97d-7c95751d89e1
-- title:
--   Original finite-activity finite simple predictable negative-mark compensation without extractor premises
-- statement:
--   For the same original Levy process and original filtration, prove a finite sum of nonnegative adapted interval-start coefficients multiplied by intrinsic negative-mark counts has the corresponding sum of compensator expectations. Each deterministic interval may overlap others. No externally supplied future extractor, independent auxiliary process or first absolute jump-size moment is assumed. It is a necessary simple-integrand building block for stopped physical source centring phys35.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys38_original_finite_simple_negative_mark_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i)) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P) =
    ∑ i ∈ S,
      (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
