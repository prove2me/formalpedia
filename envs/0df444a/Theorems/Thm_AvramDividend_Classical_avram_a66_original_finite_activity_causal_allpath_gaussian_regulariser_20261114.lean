-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a66_original_finite_activity_causal_allpath_gaussian_regulariser_20261114
-- name    : AvramDividend.Classical.avram_a66_original_finite_activity_causal_allpath_gaussian_regulariser_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T12:47:28.435683+00:00
-- url     : https://prove2.me/theorems/27e5ee5c-ca14-451c-8f92-cb1b56a4c0c3
-- title:
--   Finite negative-jump activity: causal original-source jump-removal process with everywhere cadlag raw-adapted paths
-- statement:
--   On the original uncompleted raw-filtration probability space with finite negative-jump intensity, construct an everywhere cadlag and without positive jumps raw-adapted source regulariser. On a single conull event it is the physical original process minus its compensated drift and the complete causal marked jump sum. Requires an intrinsically nonanticipative pathwise construction, with a bad-path patch that retains raw adaptation. It does not assume that a conull event is measurable in the initial filtration, and avoids adding external Gaussian randomness.
-- source:
--   Original finite-activity causal jump removal using Proved a35 physical jump sum identity, a32 finite physical residual cadlag on horizons, a30 cancellation of matched jumps, a31 finite marked consistency, and a52 conull raw-adapted source regularity. The new theorem isolates the missing every-path raw-adapted extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a66_original_finite_activity_causal_allpath_gaussian_regulariser_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        G t ω =
          X.X t ω -
          (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) -
          (∑' u : ℝ≥0,
            if 0 < u ∧ u ≤ t then
              X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
            else 0)) := by sorry
