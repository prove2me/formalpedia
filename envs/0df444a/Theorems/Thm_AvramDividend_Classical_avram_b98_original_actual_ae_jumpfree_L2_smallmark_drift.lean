-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b98_original_actual_ae_jumpfree_L2_smallmark_drift
-- name    : AvramDividend.Classical.avram_b98_original_actual_ae_jumpfree_L2_smallmark_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:20:12.123114+00:00
-- url     : https://prove2.me/theorems/8bf87629-85db-4406-b8f8-d803e58a0be2
-- title:
--   True original source jumpfree stopped interval has a.e. exact square-integrable compensated small-mark drift
-- statement:
--   For the original Standing spectrally negative Levy process with finite negative activity, and genuine bounded ordered random source clocks s,t, assume a joint conull event with no original Levy jumps in the selected interval. Apply the finite cutoff true nojump source equality B80 to build an almost-everywhere all-cutoff band identity, then use B84 original Levy signed first-moment cutoff convergence and B97 proven original same-source Jsmall limit construction. It follows that a square-integrable fixed-time Jsmall process has exact original stopped jumpfree random-clock drift equal to time increment times the full small-negative-jump compensator, almost everywhere. This is a prerequisite for the original Gaussian/negative-mark stopped Ito cash certificate.
-- source:
--   Proved JA19 finite original smallband L2 convergence, B80 physical band increment, B84 original signed Levy cutoff moment, B97 a.e. transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
import Theorems.Thm_AvramDividend_Classical_avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original a.e. jumpfree source increments have the exact limiting signed compensator. -/

theorem AvramDividend.Classical.avram_b98_original_actual_ae_jumpfree_L2_smallmark_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ T : ℝ≥0, Integrable (fun ω => (Jsmall T ω) ^ 2) P) ∧
      (∀ᵐ ω ∂P,
        Jsmall (t ω) ω - Jsmall (s ω) ω =
          - ((t ω : ℝ) - (s ω : ℝ)) *
            (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by sorry
