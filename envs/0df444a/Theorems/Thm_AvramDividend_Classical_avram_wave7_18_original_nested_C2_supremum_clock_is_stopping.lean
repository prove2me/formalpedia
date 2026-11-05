-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
-- name    : AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:27:44.887931+00:00
-- url     : https://prove2.me/theorems/6ed012a7-a127-4a5a-8866-5af09c4baf78
-- title:
--   Supremum of increasing source-specific positive-interior bounded exit clocks is an original right-continuous-filtration stopping time
-- statement:
--   Using the already Proved original single-band stopped-clock theorem for the genuine controlled post-payment reserve, each finite-stage dense-grid exit clock is a stopping time for 𝓕.rightCont. The set of original paths on which their pointwise supremum is at most t equals the countable intersection of the events τ_n≤t. Each event is measurable in the original right-continuous filtration at time t, and countable intersection preserves measurability. Thus the supremum is itself a source-space stopping time, under the exact ContDiffOn ℝ 2 positive interior domain. This does not identify the supremum with ruinTime or cap contact, and does not promote it to raw 𝓕 without right-continuity.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
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
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => ⨆ n, τ n ω) := by sorry
