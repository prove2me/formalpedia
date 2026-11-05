-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_past_weight_grid_lintegral
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_finite_past_weight_grid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:49:14.741863+00:00
-- url     : https://prove2.me/theorems/57a4e120-a75e-412a-be7a-98846df42d0c
-- title:
--   Original Lévy finite past-weighted intrinsic count-grid has exact physical expected intensity
-- statement:
--   For the genuine original spectrally negative Lévy process, any finite family of original source marked jump counts on adapted intervals weighted by nonnegative past-measurable functions satisfies an exact finite-sum expected compensated-intensity identity. Measurability of each original source count and global measurability of each weight are explicit. This composes the proved zero-origin weighted P2-E source rate with pinned Tonelli finite-sum linearity, retains infinite ENNReal rates, and supports original small-jump P3/P4 finite-simple integrands without a replacement process or extra assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_finite_past_weight_grid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (N : ι → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hNm : ∀ i ∈ S, Measurable (N i))
    (W : ι → Ω → ℝ≥0∞)
    (hWp : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hWm : ∀ i ∈ S, Measurable (W i)) :
    (∫⁻ ω, ∑ i ∈ S, W i ω * N i ω ∂P) =
      ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
