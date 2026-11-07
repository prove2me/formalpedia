-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_allclock_BV_mass_positive_DCT
-- name    : AvramDividend.Classical.avram_bv_strict6_original_allclock_BV_mass_positive_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:19:42.621198+00:00
-- url     : https://prove2.me/theorems/eba93a21-e27c-4d9d-87a0-5ccf2f94f3dd
-- title:
--   Original BV physical source mass controls positive grid errors on every finite horizon
-- statement:
--   For the authentic original BV spectrally negative Levy X under Standing, at every finite clock T, any measurable original physical-grid error dominated in absolute value by a fixed multiple of the genuine source mass |drift| T + |T drift - X(T)| and converging almost surely to zero has integrable positive parts and expected positive errors tending to zero. This removes the former T at most one restriction from the accepted random-grid DCT, while preserving the actual X mass and without using the signed dividend budget. Later source work must establish the concrete stopped-grid domination and a.e. convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_original_allclock_BV_mass_positive_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
