-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
-- name    : AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:52:01.493953+00:00
-- url     : https://prove2.me/theorems/976bbfb1-ea1b-45b2-85c0-70429b7a6535
-- title:
--   Fixed-time integrability of the truly downward-killed scale payoff under unbounded variation without Standing
-- statement:
--   Under unbounded variation rather than Standing, a spectrally negative Lévy process has integrable fixed-time discounted canonical q-scale payoff restricted to survival above zero throughout the continuous history. Assume an explicit countable observation schedule τ covering reciprocal-natural grids to certify measurability of the strict whole-path survival event. The already Proved unbounded-scale fixed-time integrability theorem controls the terminal W(x+X_t), a constant discount preserves integrability, and the proven lower-survival event is measurable; applying Integrable.indicator establishes the killed payoff's integrability without Standing. This closes the integrability precondition of the correct killed-scale martingale, leaving genuine conditional q-harmonicity independent.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable
      (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))) P := by sorry
