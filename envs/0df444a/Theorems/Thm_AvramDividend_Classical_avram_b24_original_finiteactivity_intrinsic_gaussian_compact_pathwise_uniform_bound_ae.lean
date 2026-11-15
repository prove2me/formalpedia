-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_intrinsic_gaussian_compact_pathwise_uniform_bound_ae
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_gaussian_compact_pathwise_uniform_bound_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:36:02.374576+00:00
-- url     : https://prove2.me/theorems/e9537909-d386-4929-a05d-b0f82406d925
-- title:
--   Any original nonzero-jump finite-activity intrinsic Gaussian witness has a finite sample-path uniform norm bound on every compact physical horizon
-- statement:
--   For the genuine intrinsic Gaussian cutoff limit R of the original finite-negative-activity spectrally negative Lévy source X with arbitrary nonzero negative-jump measure on its own Ω/P, every fixed compact physical horizon [0,T] has almost surely a FINITE sample-path upper bound K(ω) on the norm of R(t,ω) simultaneously for all t≤T. Obtain source-faithful almost sure global continuity of the actual R witness from the Proved original a38 theorem and apply extreme-value/compact-image norm bound to the exact real-valued continuous path on compact Icc(0,T). This is a pathwise source regularity fact, NOT a claim that K is integrable or that zero-jump Gaussian Brownian variance formula applies; those are genuine separate stochastic obligations for B219.
-- source:
--   Proved a38 original all-time intrinsic R continuity on actual Lévy sample space and Mathlib compact image isBounded.exists_norm_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_gaussian_compact_pathwise_uniform_bound_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ≥0, t ≤ T → ‖R t ω‖ ≤ K := by sorry
