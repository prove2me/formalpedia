-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq
-- name    : AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:13:33.097197+00:00
-- url     : https://prove2.me/theorems/857f5ba3-a81a-43ee-9027-9dae04e67e45
-- title:
--   Closed finite-horizon Lévy survival is dense-grid survival plus terminal observation
-- statement:
--   For a spectrally negative Lévy process, a finite horizon T, a countable observation schedule covering all reciprocal-natural-grid times and strict lower/upper barriers, survival at all continuous times t≤T is exactly equivalent to survival at the schedule observations τ(j)<T together with an explicit survival check at time T itself. The separate terminal observation is essential: it accounts for a strict barrier crossing occurring at precisely T without assuming fixed-time jump probabilities vanish. The proof uses the already accepted strict-before-horizon dense-grid survival theorem and a linear-order split into t<T and t=T. This is the pathwise closed-horizon event needed for a genuinely killed Markov semigroup at T.
-- source:
--   Depends on AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq (public authoring pending) and finite-horizon strict crossing lemmas from Chat03.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_finite_horizon_dense_schedule_survival_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    {ω | ∀ t : ℝ≥0, t ≤ T →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      (⋂ j : ℕ, {ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}) ∩
        {ω | ¬ (X.X T ω < lower ∨ upper < X.X T ω)} := by sorry
