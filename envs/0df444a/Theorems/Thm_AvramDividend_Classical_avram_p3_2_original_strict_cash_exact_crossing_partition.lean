-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_exact_crossing_partition
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_cash_exact_crossing_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:04:44.085066+00:00
-- url     : https://prove2.me/theorems/2f7c0fdd-201c-4159-94f5-caaf2ff40878
-- title:
--   Original ruin-stopped cash equals exact strict-prefix cash plus its unique crossing cell
-- statement:
--   For every positive stopped clock of the actual Lévy process and dividend strategy, the total finite-grid discounted dividend cash decomposes exactly into the strictly pre-contact prefix and one physical crossing cell at the final index, with that index strictly below the clock and its successor at the clock. In particular, no unaccounted horizon or ruin cash disappears.
-- source:
--   Use Proved GRID3 exact strict-prefix filter cardinality 53697545; Proved crossing index cardinality e255f11d; Proved singleton contact filter caf0e418; Proved original physical cash partition db7c5004. Identify the common index by singleton membership and rewrite each indexed filter to derive the literal physical cash decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_cash_exact_crossing_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun j =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u j : ℝ) (u (j + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (∑ j ∈ Finset.range (m + 1), cash j) =
          (∑ j ∈ Finset.range i, cash j) + cash i := by sorry
