-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_closed_horizon_survival_condExp_future_scale
-- name    : AvramDividend.Classical.chat04_unbounded_closed_horizon_survival_condExp_future_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:15:13.498014+00:00
-- url     : https://prove2.me/theorems/8c9f8ef4-a950-4f0e-ab15-71aeefa1826a
-- title:
--   Unbounded-variation conditional future scale expectation on closed-horizon survival
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, restrict the future scale payoff to the event of continuous-path survival through a closed horizon T. Its conditional expectation given the history at T factors as the historical survival indicator times the unconditional increment-scale expectation. This is the no-Standing counterpart of the proved standing-case closed-horizon Markov factorisation, using the proved unbounded scale integrability and past-event conditional expectation.
-- source:
--   Avram, Palmowski and Pistorius (2007); mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; helper for unbounded killed-scale optional stopping.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_past_event_scale_condExp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_closed_horizon_survival_condExp_future_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ)
    (T u : ℝ≥0) (hTu : T ≤ u) (x : ℝ) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun ω => W (x + (X.X u ω - X.X T ω))) | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun _ => ∫ ω, W (x + X.X (u - T) ω) ∂P) := by sorry
