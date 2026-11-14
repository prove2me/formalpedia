-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b103_original_physical_marked_grid_count_L1_from_true_poisson_dom
-- name    : AvramDividend.Classical.avram_b103_original_physical_marked_grid_count_L1_from_true_poisson_dom
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:55:09.498322+00:00
-- url     : https://prove2.me/theorems/aae507f4-a296-4053-9b30-a8be87576055
-- title:
--   Original finite-activity stopped physical marked-grid cardinal has finite L1 expected count under genuine Poisson count domination
-- statement:
--   Under finite original negative Levy activity and a bounded genuine sample-path-dependent stopping clock σ, the original mapped physical negative Poisson mark count in (0,σ] has finite expectation by a proved source intensity lemma. For any genuinely selected physical finite marked-cell family J(ω) whose ENNReal cardinal is pathwise dominated by this original negative source count, monotonicity of the original physical lintegral immediately proves finite expected marked-cell count. This is the analytic L1 envelope needed by the true stopped Ito mixed-source occupied-cell budget; the physical counting injection supplying hJdom is a separate marked-cell obligation (B94/B100). No global negative-mark second moment is introduced.
-- source:
--   Proved avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate, original physical Poisson count and monotonicity of lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical original marked-cell cardinality is L1 dominated by the true stopped negative-jump Poisson source. -/

theorem AvramDividend.Classical.avram_b103_original_physical_marked_grid_count_L1_from_true_poisson_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (J : Ω → Finset ℕ)
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by sorry
