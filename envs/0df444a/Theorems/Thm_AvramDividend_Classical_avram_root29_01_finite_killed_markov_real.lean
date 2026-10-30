-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_real
-- name    : AvramDividend.Classical.avram_root29_01_finite_killed_markov_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:45:28.306527+00:00
-- url     : https://prove2.me/theorems/fa5a7413-6caa-42b4-914a-bf9d5ac06caa
-- title:
--   Genuine original-Lévy finite killed Markov identity in real expectations
-- statement:
--   For any genuine spectrally negative Lévy process under P, every nonnegative Esscher parameter θ, starting real reserve x and finite horizons s,u, the real expectation of compensated Esscher terminal reward surviving the closed lower boundary to s+u equals the original-P expectation of historical survival-weighted current Esscher density times the true future survival mass F_u(x+X_s). The statement is a real Bochner-integral identity, not only ENNReal equality. It uses genuine source-level Markov disintegration and separate actual P integrability of the random-reserve weighted reward.
-- source:
--   WS1A proof draft work/avram_root29_01_finite_killed_markov_real_draft.lean. Do not submit until target a4195aa0 is canonically Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_weight_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_finite_killed_markov_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ)) ω ∂P) =
    (∫ ω : Ω,
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          (∫ ζ,
            ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
              (fun ζ => Real.exp
                (θ * X.X u ζ - (u : ℝ) *
                  laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P) := by sorry
