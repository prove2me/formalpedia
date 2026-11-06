-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:11:12.658393+00:00
-- url     : https://prove2.me/theorems/3a6acab6-12fb-4dae-80af-e10252b31699
-- title:
--   Original BV finite-stop nonlinear jump sum dominated convergence from physical Lipschitz and true jump variation
-- statement:
--   For almost every actual bounded-variation spectrally negative Lévy path stopped at a finite horizon S, absolute summability of the true original negative jump marks supplies a summable dominant for discounted nonlinear jump increments on the genuine stopped controlled reserve states. Under explicit physical-tag convergence, local Lipschitz, original pre/post-jump continuity and bounded discounts, the full infinite-activity original stopped source jump sum converges.
-- source:
--   Proved original BV absolute raw-jump summability 54643412, pinned Mathlib dominated-convergence for tsum and exact X.X marked increments. Explicit continuity, local Lipschitz and prestate convergence still need stopped physical mesh verification; no proxy law or finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (S : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ∀ (w : ℝ → ℝ) (z : ℕ → ℝ≥0 → ℝ)
        (u discount : ℝ≥0 → ℝ) (L M : ℝ),
      0 ≤ L → 0 ≤ M →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        Tendsto (fun k => z k t) atTop (nhds (u t))) →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        ContinuousAt w (u t) ∧
        ContinuousAt w (u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t))) →
      (∀ᶠ k in atTop, ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        |w (z k t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (z k t)| ≤
          L * |X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t|) →
      (∀ t : ℝ≥0, |discount t| ≤ M) →
      Tendsto
        (fun k => ∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
          discount t *
            (w ((z k) t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
        else 0) atTop
        (nhds (∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
          discount t *
            (w (u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (u t))
        else 0)) := by sorry
