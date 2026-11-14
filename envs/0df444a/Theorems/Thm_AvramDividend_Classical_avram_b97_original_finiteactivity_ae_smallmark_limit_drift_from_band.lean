-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
-- name    : AvramDividend.Classical.avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:41:23.661046+00:00
-- url     : https://prove2.me/theorems/d192c0bb-5a98-4703-bfd8-134e38c9e681
-- title:
--   Construct original a.e. square-integrable small-mark limit and inherit drift from finite-band source equality
-- statement:
--   Under finite original negative jump activity and Standing, Proved JA19 constructs an original compensated small-negative-mark process Jsmall with almost-everywhere all-time finite-band convergence and square-integrable fixed-time sections. Assume the actual original stopped random-clock finite-band increment equals its signed negative-mark compensator and that the original Levy signed moment cutoffs tend to c. On the joint conull event at both random endpoints, uniqueness of real limits gives exactly Jsmall(t)-Jsmall(s)=-(t-s)c. The Jsmall limit hypothesis is discharged by a proved same-original-source construction, not strengthened to all sample paths.
-- source:
--   Proved avram_ja19_original_finite_activity_smallband_limit_square_L1; original finite-band physical source and Levy moment limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_limit_square_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine a.e. original small-band limit produces exact jumpfree compensator drift. -/

theorem AvramDividend.Classical.avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : Ω → ℝ≥0) (c : ℝ)
    (hBand : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
        - ((t ω : ℝ) - (s ω : ℝ)) *
          (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
    (hMoment : Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 c)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ T : ℝ≥0, Integrable (fun ω => (Jsmall T ω) ^ 2) P) ∧
      (∀ᵐ ω ∂P,
        Jsmall (t ω) ω - Jsmall (s ω) ω =
          - ((t ω : ℝ) - (s ω : ℝ)) * c) := by sorry
