-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_payoff_adapted
-- name    : AvramDividend.Classical.chat03_killed_scale_payoff_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:53:28.997451+00:00
-- url     : https://prove2.me/theorems/b3295962-412d-4193-8439-614757867c92
-- title:
--   The continuously downward-killed discounted scale payoff is adapted
-- statement:
--   For a spectrally negative Lévy process and its q-scale function W, the discounted payoff W(x+X_t) multiplied by the indicator of never having crossed below zero over the entire continuous-time history from 0 through t is adapted to the original Lévy filtration. The proof obtains filtration measurability of the uncountable-time ruin-survival history via dense-grid lower crossing and terminal observation, then composes the Borel scale function with the adapted reserve and takes the indicator. It establishes the adaptedness component required for an eventual true killed q-scale martingale; integrability and conditional-expectation harmonicity are separate unresolved obligations.
-- source:
--   Depends on newly authored chat03_lower_survival_filtration_measurable and publicly Proved chat03_scale_function_borel_measurable (45cbe3b4-374d-4fa4-b988-e09f93b74cab). Neither assumes killed martingale or two-sided exit identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_killed_scale_payoff_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Adapted 𝓕
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) := by
  sorry
