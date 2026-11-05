-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
-- name    : AvramDividend.Classical.avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:57:07.083818+00:00
-- url     : https://prove2.me/theorems/b0790806-0c14-4f1f-8b60-80fd99e1d206
-- title:
--   Original all-horizon jump intensity has the genuine unit-time Tonelli identity via public mark marginal
-- statement:
--   For the actual original Lévy X, construct one σ-finite negative-supported intrinsic marked jump-intensity measure σ that controls all positive horizons and whose unit-time nonnegative weighted test integral equals the expectation of the genuine intrinsic counting-kernel mark integral for every measurable f. The same σ is chosen independently of f; identify it with each f-dependent P2-D Tonelli measure by equality on measurable sets. This is a source-exact bridge towards identifying σ with X.ν.
-- source:
--   Public Proved original P2-C all-horizon intrinsic rate and new public mark-marginal Tonelli helper, identified by Measure.ext at T=1; no private imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_public_original_mark_marginal_tonelli

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ), Measurable f →
        (∫⁻ y, ENNReal.ofReal (f y) ∂σ) =
          (∫⁻ ω, ∫⁻ p in (Ioc 0 (1 : ℝ≥0) ×ˢ (Set.univ : Set ℝ)),
            ENNReal.ofReal (f p.2) ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P)) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by sorry
