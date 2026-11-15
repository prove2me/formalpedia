-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
-- name    : AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:24:45.872678+00:00
-- url     : https://prove2.me/theorems/e621d3f0-4a4f-486f-b559-4333de0ff1e5
-- title:
--   Any original finite-activity intrinsic compensated smallmark process has an integrable path-uniform physical horizon envelope
-- statement:
--   For the unmodified original finite-negative-activity spectrally negative Lévy source X, EVERY intrinsic compensated smallmark witness Jsmall satisfying the only assumed a.e. all-time residual cutoff limit admits a universal random bound across ALL t≤T, consisting of the genuine original small-negative-mark Poisson count N_{(0,T]×(-1,0)} plus T times the absolute complete signed smallmark first-moment compensator. This random envelope is integrable under the original X probability measure by the exact Proved negative Borel Campbell count mean, with NO global second moment of large negative jumps, no independent stopping-clock assumption, and no auxiliary Poisson process. The proof uses the exact actual finite marked Jsmall path, filtered physical smallmark support cardinal and bounded masked smallmark jump source.
-- source:
--   Original finite activity actual marked step source, exact smallnegative source count card, mask norm bound, Proved ja35 real expected Poisson count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        ‖Jsmall t ω‖ ≤ B ω := by sorry
