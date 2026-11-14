-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_standing_BV_any_spatial_width_discounted_negative_mark_budget_eventually_below_positive_drift
-- name    : AvramDividend.Classical.avram_bva_a22_original_standing_BV_any_spatial_width_discounted_negative_mark_budget_eventually_below_positive_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:12:08.590224+00:00
-- url     : https://prove2.me/theorems/cfed67f7-1e38-43c6-a861-975399d007c9
-- title:
--   Original standing BV infinite-activity positive drift eventually dominates the actual discounted small-reserve negative-mark boundary budget for any shrinking spatial widths
-- statement:
--   Under precisely the original Avram standing assumptions X.Standing and X.BoundedVariation, the physical drift is automatically strictly positive by the already Proved bv_standing_drift_pos, with no extra drift assumption. For each actual positive discounted spatial boundary width sequence epsilon_n <=1 tending to zero, regardless of its rate relative to the prescribed original physical mesh, the original Levy negative-mark truncated first moment plus q*epsilon_n is strictly smaller than the genuine drift beyond a deterministic index. Combine the Proved source positive-drift consequence of Standing with the Proved arbitrary-width truncated negative mark first-moment limit. This supplies a source-specific zero-reserve budget for the remaining canonical BVA96 spatial C1 error without changing the driving process or assuming finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_standing_BV_any_spatial_width_discounted_negative_mark_budget_eventually_below_positive_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      q * ε n + (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) <
        X.drift := by sorry
