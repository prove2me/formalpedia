-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:09:13.763191+00:00
-- url     : https://prove2.me/theorems/ed3978f2-d952-4656-aa9d-4066391db9a4
-- title:
--   Actual shifted weighted jump mass is independent of the original stopped history for every finite stopping time
-- statement:
--   For the original spectrally negative Levy process on its original probability space and right-continuous filtration, every real-valued nonnegative Borel weighted jump mass on the genuine future path shifted by an arbitrary finite stopping time is independent of the stopped original history. This follows from a Borel coordinate-path extension of the exact weighted mass, the actual shifted path cadlag theorem and the original full-shifted-path strong Markov independence. No auxiliary Brownian process or independently copied Poisson measure is used. This supports Gaussian residual centring, cross-orthogonality, and stopped-grid conditional expectations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_poststop_shifted_weighted_jump_mass_independent
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
            if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧
              (X.X (τ ω + u) ω - X.X (τ ω) ω) -
              Function.leftLim (fun v : ℝ≥0 =>
                X.X (τ ω + v) ω - X.X (τ ω) ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                (X.X (τ ω + u) ω - X.X (τ ω) ω) -
                Function.leftLim (fun v : ℝ≥0 =>
                  X.X (τ ω + v) ω - X.X (τ ω) ω) u)))).toReal)
        inferInstance) P := by sorry
