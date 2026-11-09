-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_finite_grid_eventwise_centering
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_finite_grid_eventwise_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:30:16.235139+00:00
-- url     : https://prove2.me/theorems/32eb6641-4296-4d76-ac16-2dcf490b73fa
-- title:
--   Original pure-jump finite grid has zero eventwise compensated expectation
-- statement:
--   For a finite grid of original spectrally negative Levy finite-band jump-count increments, each weighted by a bounded coefficient measurable in its own right-continuous past, the integral of their sum over any event in every corresponding past is exactly zero. This preserves the original jump measure, filtration and predictable masks and is the finite-grid input to stopped-clock compensation.
-- source:
--   Original-process finite-grid composition of public Proved c97f2b53 and efff5e05, for the open stopped reward budget 71fd10ee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_past_event_integral_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump12_original_finite_grid_eventwise_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i n, s i < r i n) (hrt : ∀ i n, r i n ≤ t i)
    (hShort : ∀ i, Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i, Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc (s i) (t i) ×ˢ B i))
    (H : ι → Ω → ℝ) (K : ι → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hHAE : ∀ i, AEStronglyMeasurable (H i) P)
    (hBound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (A : Set Ω) (hA : ∀ i, MeasurableSet[𝓕.rightCont (s i)] A) :
    (∫ ω in A, ∑ i : ι, H i ω *
      ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by sorry
