-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b137_original_conull_marked_grid_count_L1_from_poisson_dominance
-- name    : AvramDividend.Classical.avram_b137_original_conull_marked_grid_count_L1_from_poisson_dominance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:45:55.162305+00:00
-- url     : https://prove2.me/theorems/6be8601c-4357-4cbb-b902-5d60af158943
-- title:
--   Original genuinely marked stopped-grid cell count is integrable under conull physical Poisson source count domination
-- statement:
--   For the exact original finite-negative-activity spectrally negative Lévy source and any bounded genuine random clock σ, suppose the cardinal of a physically marked source-grid Finset is dominated almost everywhere, on a common original conull event, by the genuine original mapped negative-jump Poisson count in the half-open interval up to σ. Then the original marked-cell cardinal has finite Lebesgue integral against the same original probability measure. The proof uses Proved original bounded-clock negative-jump Poisson count L1 intensity/rate and monotonicity of the lintegral under almost-everywhere pointwise dominance. This removes the older B103 theorem’s unnecessarily strong pathwise-for-all-samples domination, important because Lévy jump finiteness need hold only almost everywhere for finite activity and exceptional paths cannot be dismissed without conull handling.
-- source:
--   Proved avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate and Mathlib lintegral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical original marked-cell cardinality is L1 when dominated almost everywhere by the true stopped source negative Poisson jump count. -/

theorem AvramDividend.Classical.avram_b137_original_conull_marked_grid_count_L1_from_poisson_dominance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (J : Ω → Finset ℕ)
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by sorry
