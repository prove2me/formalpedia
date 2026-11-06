-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:08:32.741096+00:00
-- url     : https://prove2.me/theorems/c0698d63-49f6-467f-b895-2dcd0dcf79ff
-- title:
--   Original stopped strict physical-grid prefix ends below tau whenever the original stopped time is positive
-- statement:
--   The literal original stopped physical-grid right-endpoint cells form a finite prefix range k, and for every path with tau>0 that prefix's terminal clock u k remains strictly below tau. This source-exact cutoff can therefore be passed to both accepted original strict-prefix discounted Stieltjes budgets f6458d58 and 8eddbe03. The tau=0 branch is deliberately left separate for the already accepted original zero-clock budget; no replacement process, cap or ruin assumption is introduced.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
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
    ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) = Finset.range k ∧
      (0 < τ → u k < τ) := by sorry
