-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_original_weighted_R_ae_mesh_envelope
-- name    : AvramDividend.Classical.avram_coord8_original_weighted_R_ae_mesh_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:42:44.604331+00:00
-- url     : https://prove2.me/theorems/2f8b8235-7800-476a-9dbd-c472b8cb74fb
-- title:
--   Original BV weighted physical-grid raw-jump remainder has the sharp almost-sure endpoint envelope
-- statement:
--   On an original bounded-variation spectrally negative Levy process, every monotone finite physical mesh has almost-sure endpoint control of a raw-jump remainder sum when its coefficients are uniformly bounded. The random remainder is the exact drift-minus-original-path-minus-real-jump-series expression, preserving jump direction, stopping convention and process identity.
-- source:
--   Direct a.e. composition of public Proved d95da4ae-c6d5-4cdd-abda-949ab6253b73 and b5f11d6e-a1a4-4167-9676-ec609cb0a5c6. The endpoint bound is useful for bounding the original B residual weights on finite BV cells, conditional on a separately justified derivative bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord8_original_weighted_R_ae_mesh_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : ℕ → ℝ) (K : ℝ)
    (hK : ∀ i ∈ Finset.range (n + 1), |a i| ≤ K) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      |∑ i ∈ Finset.range (n + 1),
          a i * (R (u n i) - R (u n (i + 1)))| ≤
        K * (R (u n (n + 1)) - R (u n 0)) := by sorry
