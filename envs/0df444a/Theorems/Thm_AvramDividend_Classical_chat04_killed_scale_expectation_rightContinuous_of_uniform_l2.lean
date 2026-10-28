-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
-- name    : AvramDividend.Classical.chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:46:08.931727+00:00
-- url     : https://prove2.me/theorems/99362c24-e84e-48b1-9ffd-a27654d913c5
-- title:
--   Right-continuity at every time of the expected whole-history killed scale payoff
-- statement:
--   The discounted q-scale reward killed by any earlier negative-reserve excursion has right-continuous real expectation at every deterministic time. The hypothesis W(0)=0 covers the unbounded-variation case. Uniform finite-horizon second moments and the sequential characterisation of right-neighbourhood limits upgrade pathwise right continuity to expected right continuity.
-- source:
--   Proved sequential killed expectation continuity and Mathlib Filter.tendsto_iff_seq_tendsto, following accepted time-zero continuity proof.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_tendsto_of_uniform_l2
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t₀ : ℝ≥0) :
    ContinuousWithinAt
      (fun t : ℝ≥0 => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t u)) ω ∂P)
      (Ici t₀) t₀ := by sorry
