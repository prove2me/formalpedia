-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
-- name    : AvramDividend.Classical.avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:26:39.648561+00:00
-- url     : https://prove2.me/theorems/9073b48f-86d0-44af-b29f-de07e5aeb28b
-- title:
--   Increasing original-source positive-interior bounded stopping clocks cover every time strictly below their supremum
-- statement:
--   For arbitrary nested finite positive-interior bands and nondecreasing bounded horizons, define the countable family of dense-grid first-exit clocks on the actual original post-payment reserve and its pointwise supremum. Each clock is a stopping time for 𝓕.rightCont by the previously Proved source stopping theorem. Every consecutive pair is monotonically ordered by the published nested-clock lemma. For any original path and extended nonnegative time t, t is strictly below the supremum clock if and only if t lies strictly below some finite-stage clock, using lt_iSup_iff. This gives genuine countable localisation coverage up to the supremum; the separate identification of that supremum with physical ruin/cap exit is explicitly not claimed.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let τSup : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, τ n ω
    (∀ n, IsStoppingTime 𝓕.rightCont (τ n)) ∧
      (∀ n ω, τ n ω ≤ τ (n + 1) ω) ∧
      ∀ ω (t : WithTop ℝ≥0), t < τSup ω ↔ ∃ n, t < τ n ω := by sorry
