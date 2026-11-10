-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:13:34.953831+00:00
-- url     : https://prove2.me/theorems/dde4ee7f-47ce-4dec-959a-04f891f893c4
-- title:
--   Original and horizon-frozen marked jump measures agree on every nonnegative Borel mark weight
-- statement:
--   Source-exact original-path prefix observability bridge. For every sample point and deterministic horizon, a nonnegative Borel mark weight integrates identically against actual original jumps and the frozen original path's jumps over the strict-positive closed-horizon window. It is needed to transfer the existing Borel measurable cadlag jump-functional result through original filtration measurable frozen paths, and thereby recover the signed physical finite Gaussian cutoff terms. No Gaussian factor or independent auxiliary Lévy process is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_generic_marked_window_count_any_horizon
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)))) := by sorry
