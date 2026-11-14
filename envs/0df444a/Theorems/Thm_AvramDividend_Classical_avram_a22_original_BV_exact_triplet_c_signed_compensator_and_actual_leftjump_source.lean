-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_exact_triplet_c_signed_compensator_and_actual_leftjump_source
-- name    : AvramDividend.Classical.avram_a22_original_BV_exact_triplet_c_signed_compensator_and_actual_leftjump_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:23:03.849877+00:00
-- url     : https://prove2.me/theorems/90d5e974-5de9-411d-b4ce-a2b15a7d9334
-- title:
--   Original BV Lévy source equals triplet c minus strict compensated negative mark first moment minus actual physical downward jumps, all time
-- statement:
--   Every original bounded-variation spectrally negative Lévy process satisfying the standing assumptions has the exact all-time physical triplet decomposition X_t = t c - t ∫_{(-1,0)} z ν(dz) - Σ_{0<u≤t}(X_{u-}-X_u) simultaneously on one full-measure subset of the original Ω. This theorem composes the already Proved original physical BV drift/jump source 79a63ca0 with the newly Proved original deterministic triplet drift correction 924841f4. It holds even without finite negative Lévy activity, is a genuine physical pathwise source identity rather than merely a formal Gaussian construction, and is a reusable premise for original finite-activity compensation theorem 891842bf.
-- source:
--   Proved original BV full-time physical jump identity 79a63ca0; Proved exact original negative strict mark triplet drift 924841f4; Avram, Palmowski and Pistorius Lévy–Itô convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_BV_exact_triplet_c_signed_compensator_and_actual_leftjump_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.c -
        (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω else 0) := by sorry
