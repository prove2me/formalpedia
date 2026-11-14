-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b100_original_finite_negativeactivity_source_grid_marked_count_ae
-- name    : AvramDividend.Classical.avram_b100_original_finite_negativeactivity_source_grid_marked_count_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:48:39.621414+00:00
-- url     : https://prove2.me/theorems/af8104cf-e617-446d-94e9-8f26fa2d2fe6
-- title:
--   Finite original negative activity yields genuine finite source jump-time witnesses controlling every occupied monotone physical grid cell
-- statement:
--   On a P-conull event obtained from the original finite-negative-activity Levy theorem, every bounded interval [0,T] has finitely many genuine nonzero original source jump times. Construct their exact Finset F with the same genuine left-limit source jump membership. For any finite family J of occupied cells of an arbitrary monotone time grid, assume each marked cell has an original source jump witness in that cell belonging to F. Choose one original source jump per cell; the proved original monotone-grid index uniqueness makes the choice injective across J. Finset.card_le_card_of_injOn proves J.card at most F.card. This is the exact finite-activity pathwise source marked-cell domination needed for mixed stopped Ito energy, with no global negative jump second moment or invented random source.
-- source:
--   Proved avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae, Proved avram_wave7_06_monotone_marked_grid_index_unique, pinned Mathlib Finset.card_le_card_of_injOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite original activity supplies actual source jump-time witnesses bounding every occupied physical cell. -/

theorem AvramDividend.Classical.avram_b100_original_finite_negativeactivity_source_grid_marked_count_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0,
          u ∈ F ↔ 0 < u ∧ u ≤ T ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        (∀ J : Finset ℕ,
          (∀ i ∈ J, ∃ u ∈ F,
            u ∈ Ioc (grid i) (grid (i + 1))) →
          J.card ≤ F.card) := by sorry
