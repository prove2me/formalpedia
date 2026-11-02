-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
-- name    : AvramDividend.Classical.avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:11:01.242427+00:00
-- url     : https://prove2.me/theorems/7a277885-02a8-4e96-9d65-6dfc94bb4015
-- title:
--   Actual initial/future compensator rectangles and a true finite physical clock force local finite original-source mark-band mass
-- statement:
--   For the original spectrally negative Lévy marked occupation MT=M.restrict S, with exact source K, M=P.bind K and an actual finite rightCont predictable physical clock μ and source intensity N=μ.prod(ν restricted to negative marks), assume the genuine future rectangle source compensation law. For any measurable negative-mark band B of finite canonical Lévy intensity, deduce MT(univ×B) is finite. The proved Chat01-derived physical-clock theorem supplies the initial rectangle; the assumed future rectangle at time 0 supplies the positive-time sector; the disjoint chronological decomposition into time 0 and t>0 and finite product intensity force finite total source occupation. This removes the otherwise explicit local-finiteness condition of the general stopped compensation theorem once future source law is established.
-- source:
--   Chat03 f04c5651 Proved; Chat02-C c79643ac/d884e388; source SpectrallyNegativeLevy and actual jump kernel; mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBfinite : (X.ν.restrict (Iio (0 : ℝ))) B < ∞)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C') =
        N ((Set.Ioi i ×ˢ A) ×ˢ C')) :
    MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ∞ := by sorry
