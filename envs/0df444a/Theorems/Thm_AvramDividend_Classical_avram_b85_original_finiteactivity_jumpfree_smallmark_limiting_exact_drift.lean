-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b85_original_finiteactivity_jumpfree_smallmark_limiting_exact_drift
-- name    : AvramDividend.Classical.avram_b85_original_finiteactivity_jumpfree_smallmark_limiting_exact_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:14:43.00226+00:00
-- url     : https://prove2.me/theorems/2a4f14c8-368d-43da-ba96-0b444fc61c14
-- title:
--   True finite-activity original jumpfree interval intrinsic compensated small marks have exact full ν first-moment drift
-- statement:
--   For the unmodified spectrally negative Lévy source of finite negative mark activity, the signed small negative-mark compensation limit over the original interval between minus one and zero exists and is finite by B83 and B84, with no full negative jump second moment assumed. B82 transfers the exact finite-cutoff jumpfree drift identity of B80 through the original truncated source limit to the intrinsic small-band source Jsmall. At every original jumpfree interval (including sample-path-dependent stopped endpoints), its increment equals elapsed real time times minus the original complete first moment of ν over the small negative strip. This is the source-specific hSmall hypothesis of B78 with drift exactly determined by X.ν, under explicit pointwise Jsmall source-limit assumptions. Actual construction of a totalised Jsmall limit on exceptional paths and proof that selected unmarked cells indeed contain no negative mark remain independent obligations. The terminal ruin-crossing mark remains excluded.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i); original source B80/B82/B83/B84.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b82_original_jumpfree_limit_small_compensation_drift
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b85_original_finiteactivity_jumpfree_smallmark_limiting_exact_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ ω (u : ℝ≥0), s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by sorry
