-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match
-- name    : AvramDividend.Classical.bv_esscher_canonical_scaled_tail_real_kernel_match
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:35:52.646168+00:00
-- url     : https://prove2.me/theorems/e7ad670a-befb-4143-a872-ab909dba8448
-- title:
--   Canonical Esscher tail measure exactly matches the drift-normalised real renewal kernel
-- statement:
--   For a bounded-variation spectrally negative Lévy process at the positive Esscher root, construct the continuous antitone positive subunit real renewal kernel and prove that its exact Lebesgue density measure is the inverse-drift multiple of the canonical discounted Lévy jump-tail measure. This resolves the normalisation and existential witness mismatch in the scaled zero-barrier renewal proof.
-- source:
--   Proved bv_esscher_root_positive_subunit_kernel_package (7d3344ce-1a22-490c-9e8c-3e093c60ec36), finite discounted first moment, and the scaled strict-tail real-density identity.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_scaled_drift_real_density
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_scaled_tail_real_kernel_match
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (k : ℝ → ℝ) (ρ : ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn k (Ioi (0 : ℝ)) ∧
      AntitoneOn k (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → k t = 0) ∧
      (∀ t : ℝ, 0 ≤ k t) ∧
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ ∧
      (ENNReal.ofReal X.drift)⁻¹ •
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) =
        (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (k t)) := by sorry
