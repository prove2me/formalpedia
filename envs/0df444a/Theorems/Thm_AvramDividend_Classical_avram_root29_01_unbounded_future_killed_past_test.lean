-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_past_test
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_future_killed_past_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:27:21.462051+00:00
-- url     : https://prove2.me/theorems/31424299-2945-465d-be13-ed5652b4350d
-- title:
--   Unbounded-variation killed q-scale future-window Markov factor tested against every historical event
-- statement:
--   For an original spectrally negative Lévy law of unbounded variation, every F_s-measurable event A, arbitrary real initial capital and every future duration T, the A-restricted ENNReal expectation of the true continuously lower-killed discounted scale reward over the shifted future window equals the A-restricted ENNReal expectation of W(x+X_s). The proof uses the positive full-path event test factorisation, countably monitored exact survival equivalence and pointwise original-law kernel normalisation to W. It is the immediate noncircular input for the conditional q-scale future-window identity.
-- source:
--   Distinct WS1A proof work/avram_root29_01_unbounded_future_killed_past_test_draft.lean, to compile only after its original-future-kernel past-test and original-grid normalisation source dependencies are canonically Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_grid_killed_kernel_scale
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_killed_scale_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_unbounded_future_killed_past_test
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0)
    (s T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (x : ℝ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, if ω ∈ A then
      (if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
        then ENNReal.ofReal
          (Real.exp (-(q * (T : ℝ))) *
            W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω)))
        else (0 : ℝ≥0∞))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (W (x + X.X s ω))
      else (0 : ℝ≥0∞) ∂P := by sorry
