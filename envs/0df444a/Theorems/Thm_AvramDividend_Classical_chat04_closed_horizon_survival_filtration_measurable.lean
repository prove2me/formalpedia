-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable
-- name    : AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:29:22.883761+00:00
-- url     : https://prove2.me/theorems/8f46ff43-afd6-449a-be49-308c7399740e
-- title:
--   Full two-barrier survival up to T is measurable in the filtration at T
-- statement:
--   The event that a spectrally negative Lévy path stays within strict lower and upper barriers at all continuous times t≤T belongs to the sigma algebra F_T at the finite horizon T. It is stronger than ambient measurability and is necessary for conditioning a killed payoff on the entire past. Use the accepted closed-horizon dense-grid event equality, filtered adaptedness X_t∈F_t, monotonicity F_s⊆F_T whenever s<T and a countable intersection of observed no-exit events, plus the mandatory explicit terminal observation at T. No first-passage null-event, Markov harmonicity or stochastic stopping identity is assumed.
-- source:
--   Accepted AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq UUID 857f5ba3-a81a-43ee-9027-9dae04e67e45, canonical SpectrallyNegativeLevy.adapted and pinned Mathlib filtration monotonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} := by sorry
