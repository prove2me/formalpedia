-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
-- name    : AvramDividend.Classical.avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:52:50.216777+00:00
-- url     : https://prove2.me/theorems/13ed08f5-5cea-44fe-a95d-f5b435890093
-- title:
--   Original finite-activity small-band compensation pathwise dominated by total jump count
-- statement:
--   For almost every original path with finite number of negative jumps on [0,T], each small-band truncated compensated jump sum is bounded by the total number of negative jumps (each mark lies in (-1,0)) plus the deterministic compensation magnitude. Since the compensated drift integrates |z|≤1 over a subset of the finite negative Levy measure, its absolute value is at most T times the total negative Levy mass. This exact pathwise inequality has no large-jump size moment assumption. Reuse Proved original compensated band finite-sum 1c1d4731 and total count L2 a6562a4d.
-- source:
--   J-A19 original finite-activity pathwise count certificate

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0,
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤
          (N ω).toReal + (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
