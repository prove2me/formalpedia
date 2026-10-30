-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws
-- name    : AvramDividend.Classical.avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:36:58.558397+00:00
-- url     : https://prove2.me/theorems/275d0cb6-b69f-45c3-9f0e-cbe59626e268
-- title:
--   Canonical Brownian motion constructs an actual Gaussian spectrally negative Lévy process once the filtered increment laws are supplied
-- statement:
--   For the actual projective-limit Gaussian Brownian motion, fix a filtration under which the drift-minus-one path is adapted and whose future increments are independent of the past; suppose the natural stationary-increments identity. Then there exists an actual SpectrallyNegativeLevy over gaussianLimit with exactly the canonical Brownian path, triplet drift -1, Gaussian coefficient 1 and zero jump measure. All remaining fields of the process structure, including no-positive-jump cadlag regularity and the full exponential Lévy-Khintchine law, follow from already Proved genuine Brownian theorems. This isolates filtered independence as the last substantial step for a concrete model witness in the UBV counterexample.
-- source:
--   Canonical drifted Brownian path regularity 3b92f98a-fadc-4ddb-aa18-580d0df92b86; genuine real-time Brownian bridge 6b447517-ee65-42fd-aa06-1faa205162a5; original Gaussian Lévy Laplace law 2b64f355-76e8-4132-87f7-59710bdff7dc. Exact 70-line source remotely elaborated without errors to the intentional sentinel, private job b384435e-ef88-474c-a15f-50a9761e5885, SHA 0c93d60b4ee142ff293156deddcd48c6069cf4055b4e028b48e145769dba222c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_cadlag_no_positive_jumps
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_levy_laplace

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
open LevyStochCalc.Brownian

theorem AvramDividend.Classical.avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
    (hadapt : Adapted 𝓕
      (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)))
    (hindep : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω : ℝ≥0 → ℝ =>
          (brownian t ω - brownian 0 ω - (t : ℝ)) -
          (brownian s ω - brownian 0 ω - (s : ℝ))) inferInstance)
        (𝓕 s) gaussianLimit)
    (hstationary : ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib
        (fun ω : ℝ≥0 → ℝ =>
          (brownian t ω - brownian 0 ω - (t : ℝ)) -
          (brownian s ω - brownian 0 ω - (s : ℝ)))
        (fun ω : ℝ≥0 → ℝ =>
          brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
        gaussianLimit gaussianLimit) :
    ∃ X : SpectrallyNegativeLevy gaussianLimit 𝓕,
      X.X = (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)) ∧
      X.c = -1 ∧ X.σ = 1 ∧ X.ν = 0 := by sorry
