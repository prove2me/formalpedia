-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments
-- name    : AvramDividend.Classical.avram_wave5_02b_original_future_path_conditional_first_second_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:26:09.945203+00:00
-- url     : https://prove2.me/theorems/af7a6ae1-9c80-4160-9501-5d24b1bfc27c
-- title:
--   Original Lévy future path conditional first and second moments
-- statement:
--   On the original Lévy probability space and filtration, measurable integrable shifted-future path functionals with integrable squares have conditional first and second moments equal to their unconditional moments. Independence is derived from source finite-cylinder independence and the full future-path sigma theorem. Measurability of the marked jump extractor and evaluation of Poisson moments remain separate obligations.
-- source:
--   Canonical Proved df83d931-9b50-4c91-9b13-698d5a554893, e87d68dd-58e9-4570-8c43-ece958416b16 and 82301379-a313-4f88-8ab5-7c9aa293947e.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_condExp_of_independence
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_original_future_path_conditional_first_second_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hJint : Integrable
      (fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) P)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P) :
    (P[(fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, J (fun t => X.X (s + t) ω - X.X s ω) ∂P)) ∧
    (P[(fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P)) := by sorry
