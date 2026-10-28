-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_levy_band_zero_count_laws
-- name    : AvramDividend.Classical.ae_early_downward_jumps_of_levy_band_zero_count_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:02:13.052924+00:00
-- url     : https://prove2.me/theorems/85823b83-fe61-472d-a575-014df1938870
-- title:
--   Actual finite-band Poisson zero-count laws imply early downward jumps for infinite Lévy negative activity
-- statement:
--   Suppose a spectrally negative Lévy process has infinite negative-jump intensity and count variables for finite negative-jump bands whose zero-count events have the precise Poisson law with intensities δ_k ν((−∞,−1/(n+1)]). Assume paths with no negative jump before δ_k have zero counts. The proven Lévy intensity divergence, Poisson null-event theorem and cofinal almost-sure jump-grid theorem imply genuine downward sample-path jumps arbitrarily near zero almost surely. This precisely isolates the still-unproved construction of the actual jump-band counting law rather than claiming it follows from the intensity hypotheses alone.
-- source:
--   Proved negative_jump_real_poisson_rates_tendsto_top [25e87aea-e2cc-4603-a440-f9c9d277ee8d], zero_probability_of_poisson_count_no_jump_event [aac9e95d-3e37-4c4a-952c-c53f64ab442a], ae_early_downward_jumps_of_null_no_jump_grid [76ccf378-0f33-404c-a0d4-912b94c5f620]. Needed for Open ae_early_downward_jumps_of_infinite_negative_activity [ff758fb4-87e5-4eec-b153-b6135498ca04].

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_zero_probability_of_poisson_count_no_jump_event
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_null_no_jump_grid

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_early_downward_jumps_of_levy_band_zero_count_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (δ : ℕ → ℝ≥0) (hδpos : ∀ k, 0 < δ k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k, δ k < ε)
    (counts : ℕ → ℕ → Ω → ℕ)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp
          (-((δ k : ℝ) *
            (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l := by sorry
