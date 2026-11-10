-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:15:20.207841+00:00
-- url     : https://prove2.me/theorems/59ff5fd7-1b7c-43dc-8aeb-bc543225d4ce
-- title:
--   Actual original weighted future-window jump mass is independent of the original stopped past
-- statement:
--   Let the original spectrally negative Levy source be observed up to an arbitrary finite stopping time in its own right-continuous filtration. For any nonnegative Borel mark weight and future window length, the weighted original jump mass strictly after that stopping time and through the future right endpoint is independent of the stopped history. This follows from exact samplewise weighted marked-jump transport to the genuine shifted original increment path, and the latter's source-level stopped-history independence. The direct stopped-window result is a necessary input to original compensated jump orthogonality and Gaussian residual martingale increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω =>
          (∫⁻ p : ℝ≥0 × ℝ,
            if τ ω < p.1 ∧ p.1 ≤ τ ω + T then g p.2 else 0 ∂
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)
        inferInstance) P := by sorry
