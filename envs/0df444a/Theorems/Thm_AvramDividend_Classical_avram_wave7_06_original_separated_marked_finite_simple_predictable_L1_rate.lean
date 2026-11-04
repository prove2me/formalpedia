-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_finite_simple_predictable_L1_rate
-- name    : AvramDividend.Classical.avram_wave7_06_original_separated_marked_finite_simple_predictable_L1_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-03T07:07:51.884456+00:00
-- url     : https://prove2.me/theorems/bbab4968-b713-43da-a334-461b7689663a
-- title:
--   Actual original Lévy finite-grid predictable marked-cell L¹ intensity for arbitrary UBV/BV separated bands
-- statement:
--   For the true original Lévy process with its original filtration, a finite sum of predictable nonnegative weighted marked-jump counts on deterministic future rectangles has expectation equal to the sum of P-past-weight means times interval lengths times ν of each separated negative Borel mark set. This has no bounded variation premise, and depends on the separately honest upstream original ν intensity result.
-- source:
--   W7-06 finite simple predictable compensated jump measure from the same original process; consumers W7-07/W7-08, step toward L² approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave7_06_original_separated_marked_finite_simple_predictable_L1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s T : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (B : ℕ → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (ε : ℕ → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (hBsep : ∀ i ∈ S, B i ⊆ Iic (-(ε i))) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω ∂P) *
      ((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by sorry
