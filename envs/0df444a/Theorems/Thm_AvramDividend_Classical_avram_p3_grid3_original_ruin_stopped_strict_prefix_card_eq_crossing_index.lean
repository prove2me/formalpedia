-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:24:15.277012+00:00
-- url     : https://prove2.me/theorems/e255f11d-cb46-4055-88b3-1919a26c5786
-- title:
--   Original strict stopped-grid finite-cardinality prefix is exactly the physical ruin crossing cell index
-- statement:
--   For positive stopped time, the original min-clipped physical clock has a crossing index i with u(i)<tau=u(i+1). Monotonicity then forces exactly the earlier right endpoints j+1<=i to be strictly before tau. Consequently, the canonical finite-cardinality strict prefix index is exactly i. This gives a deterministic-on-each-path formula identifying the last fully strict physical cell and the single crossing cash cell for source-exact Stieltjes limits, without a surrogate process or unproved measurability premise.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let k : ℕ :=
      ((Finset.range (m + 1)).filter
        (fun j => u (j + 1) < τ)).card
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
        u (i + 1) = τ ∧ k = i := by sorry
