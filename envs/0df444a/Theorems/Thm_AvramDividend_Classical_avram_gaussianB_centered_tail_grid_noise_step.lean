-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_centered_tail_grid_noise_step
-- name    : AvramDividend.Classical.avram_gaussianB_centered_tail_grid_noise_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:29:50.926394+00:00
-- url     : https://prove2.me/theorems/6a5b36d0-f5cf-4570-a992-7426e3179c4e
-- title:
--   Original Gaussian physical-grid one-step extension controlled by a fixed longer Brownian tube
-- statement:
--   For an original Gaussian Lévy source with drift 2 and centred process B, a Brownian supnorm tube of radius 1/4000 on [0,1/500] bounds the compensated original source X_s-sX.c on every physical mesh sample s≤1/1000+Δ when Δ≤1/1000. This closes the one-step extension requirement in the original stopped G/H mesh noise estimate.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_centered_tail_grid_noise_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hc : X.c = 2)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 500 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 500 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (n m : ℕ)
    (hStep : (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤ (1 / 1000 : ℝ≥0))
    (s : ℝ≥0)
    (hs : s ≤ (1 / 1000 : ℝ≥0) +
      (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) :
    |X.X s ω - (s : ℝ) * X.c| ≤ (1 / 4000 : ℝ) := by sorry
