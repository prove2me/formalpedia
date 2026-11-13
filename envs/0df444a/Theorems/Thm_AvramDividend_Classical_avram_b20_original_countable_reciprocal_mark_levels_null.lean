-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_original_countable_reciprocal_mark_levels_null
-- name    : AvramDividend.Classical.avram_b20_original_countable_reciprocal_mark_levels_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:59:35.763416+00:00
-- url     : https://prove2.me/theorems/60980559-55a5-4aca-bc7c-8a9e473745ea
-- title:
--   Original BV Lévy process has no negative jumps at any reciprocal cutoff level, on all integer horizons
-- statement:
--   Standing bounded-variation Lévy processes have diffuse negative-mark intensity. The actual original marked jump measure charges none of the countable family of reciprocally indexed negative mark singletons, on any integer clock. The theorem is a single almost-sure statement uniform over all horizons and cutoffs.
-- source:
--   Direct consequence of Proved source-exact original separated negative Borel mark intensity formula avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate, Proved Standing/BV atomless levyMeasure_singleton_null_of_standing_boundedVariation, and Proved original marked source countable zero-mean union avram_p2_f_weighted_original_zero_origin_means_countable_rectangles_union_ae_zero. Needed for inclusive versus strict cutoff comparison in 59ca0406.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_original_countable_reciprocal_mark_levels_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {t : ℝ≥0 |
          0 < t ∧ X.X t ω -
            Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (⋃ p : ℕ × ℕ, Ioc (0 : ℝ≥0) (p.1 : ℝ≥0) ×ˢ
          ({-(1 / ((p.2 : ℝ) + 1))} : Set ℝ)) = 0 := by sorry
