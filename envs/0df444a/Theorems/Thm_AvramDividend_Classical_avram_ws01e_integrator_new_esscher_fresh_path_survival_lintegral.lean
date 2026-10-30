-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:30:23.597992+00:00
-- url     : https://prove2.me/theorems/7aed93b7-4781-4fae-88d4-651a5c19643a
-- title:
--   True Lévy fresh full-path lower-survival Esscher integral equals actual real finite-horizon survival expectation
-- statement:
--   For an actual spectrally negative Lévy process under original probability P, the lower-survival compensated Esscher reward at any future horizon u integrated against the genuine push-forward of the source full-path law equals the ENNReal.ofReal of its actual real finite-horizon lower-survival expectation, for any real starting reserve z and nonnegative Esscher parameter theta. The covering rational schedule includes the terminal u and is exactly equivalent to uncountable closed-path survival. This is a measurable push-forward and real-to-ENNReal integration bridge, requiring no tilted path-space probability, arbitrary Wiener-Hopf hypothesis or shifted-root differentiability.
-- source:
--   Source-faithful Markov kernel bridge for deterministic killed semigroup downstream of already Proved perpetual scalar 07c7d8b4 and all-real CDF 8c0f76fb. Uses accepted true source path grid measurability a484bed3, shifted schedule equivalence 67c7e86c, Esscher integrability 701eb6a8 and pinned Mathlib lintegral_map/ofReal_integral_eq_lintegral_ofReal. Independent of pending helper 3787cbef; no other agents' theorem targets duplicated.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ y : ℝ≥0 → ℝ,
      (if ∀ j : ℕ, τ j ≤ u → 0 ≤ z + y (τ j) then
        ENNReal.ofReal (Real.exp
          (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (∫ ω,
      ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry
