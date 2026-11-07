-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_reuse8_nonintegrable_negative_grid_L1
-- name    : AvramDividend.Classical.avram_reuse8_nonintegrable_negative_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:34:22.817883+00:00
-- url     : https://prove2.me/theorems/5bc6da94-f3d3-49e7-8fab-1fdbecb7cff9
-- title:
--   Grid payoff integrability under a nonintegrable negative drift and vanishing-positive-error budget
-- statement:
--   For nonnegative measurable finite-grid payoffs, an integrable compensated term, an integrable positive error and a merely almost-everywhere nonpositive drift give payoff L1 control. The negative drift need not be integrable.
-- source:
--   Reusable integrability implication for original BV Fatou leaf 4612f9a8. The already Proved 0aa36d8b supplies the exact original negative-generator sign, while the physical-grid F M B E identity remains a separate source-level obligation. This helper avoids suspect 5df846f9 generator-cell L1.

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_reuse8_nonintegrable_negative_grid_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hMI : ∀ n, Integrable (M n) P)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ b + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, Integrable (F n) P := by sorry
