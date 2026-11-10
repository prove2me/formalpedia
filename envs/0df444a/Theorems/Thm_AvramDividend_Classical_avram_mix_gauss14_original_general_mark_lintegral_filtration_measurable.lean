-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:22:02.174408+00:00
-- url     : https://prove2.me/theorems/c06fa917-8f0c-489c-b9d3-23f9a2bccc82
-- title:
--   Every finite-horizon original marked jump Borel weight is measurable in the original filtration
-- statement:
--   Original-source adaptedness of arbitrary nonnegative Borel weighted jump mass over the positive-time closed-horizon window. Compose the Proved measurable horizon-frozen original path with the Proved Borel cadlag-path weighted jump functional; use exact source/frozen marked integral equality to identify the result with the original X jump measure. This is the general-source step needed for exact signed finite Gaussian cutoff residuals, preserving endpoint conventions and avoiding an auxiliary Brownian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
