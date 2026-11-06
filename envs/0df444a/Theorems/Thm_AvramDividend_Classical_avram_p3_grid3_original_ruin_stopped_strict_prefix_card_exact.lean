-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:13:35.342716+00:00
-- url     : https://prove2.me/theorems/53697545-d418-4975-a3f2-363927953104
-- title:
--   Canonical explicit strict stopped-grid prefix index is the cardinal of the original interior-cell filter
-- statement:
--   Replace the existential stopped physical strict-prefix index by the explicit cardinality of the actual original-process strict-interior cell filter. The cardinal lies below m+1 and the filtered indices equal exactly range k, by the Proved original monotone stopped-grid prefix theorem. This is a source-exact canonical formula for the omega-dependent prefix needed in future measurability of finite-grid random sums; no selected witness from a surrogate process or external choice is used.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
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
        (fun i => u (i + 1) < τ)).card
    k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) = Finset.range k := by sorry
