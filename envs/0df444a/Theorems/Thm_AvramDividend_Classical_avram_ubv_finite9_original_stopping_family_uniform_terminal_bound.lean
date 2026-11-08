-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:22:34.824199+00:00
-- url     : https://prove2.me/theorems/31e1e2d3-0f05-4a13-a500-777ef34efcf9
-- title:
--   Uniform finite-cap original terminal payoff bound across every stopping localisation index
-- statement:
--   For one finite cap and one continuous payoff, a single deterministic bound controls the original post-right-payment piecewise stopped surplus value w(W k ω) for all localisation indices k and paths ω. The bound is independent of each stopping clock and accommodates time-zero, horizon, and ruin alternatives. This is the uniform terminal control needed for a subsequent UI/limit theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ω, |w (W k ω)| ≤ B := by sorry
