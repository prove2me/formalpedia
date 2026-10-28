-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable
-- name    : AvramDividend.Classical.chat04_shifted_lower_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:34:00.604996+00:00
-- url     : https://prove2.me/theorems/33f5f781-348a-45c5-a3d4-d801e47eec48
-- title:
--   Measurability of the shifted reserve's closed-horizon nonruin event
-- statement:
--   Assuming an observation schedule covering reciprocal-natural time grids, the exact closed-horizon event that a Lévy reserve started at x remains nonnegative at every earlier time is measurable. This reformulates the already Proved lower-barrier survival filtration theorem with barrier -x and is needed to apply the killed L² bound and Vitali expectation-convergence lemma to the truly whole-history killed q-scale reward.
-- source:
--   Direct import of Proved chat03_lower_survival_filtration_measurable UUID 398891d8 and filtration monotonicity. Downstream: positive-reserve killed expected-scale initial continuity, then killed renewal a885f0b3, stopped exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_shifted_lower_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (x : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∀ s : ℝ≥0,
      s ≤ t → 0 ≤ x + X.X s ω} := by sorry
