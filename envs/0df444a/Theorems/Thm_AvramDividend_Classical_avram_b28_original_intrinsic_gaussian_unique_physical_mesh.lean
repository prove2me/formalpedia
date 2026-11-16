-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_original_intrinsic_gaussian_unique_physical_mesh
-- name    : AvramDividend.Classical.avram_b28_original_intrinsic_gaussian_unique_physical_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:44:21.282485+00:00
-- url     : https://prove2.me/theorems/d188880a-c295-40dc-a2b7-d40e24f5b677
-- title:
--   The exact original physical-grid stopped Gaussian source is independent of the choice of cutoff-limit version
-- statement:
--   Given any two random process versions R and B that almost surely share the same exact original intrinsic Gaussian truncated-residual cutoff limits at all physical times, uniqueness of real limits yields indistinguishable values R_t=B_t for all t on a common full-probability event. Consequently every finite bounded-predictable original physical-grid stopped Gaussian mesh sum, with the exact stop mask if sigma<=a_i then 0, is unchanged when R is replaced by B. This isolates the a.e. pathwise source-version identification required by the B25 original Brownian/Poisson obstruction; no independence or Gaussian process construction is presumed.
-- source:
--   Original intrinsic truncated-residual definition 33b0fa2b and B25 fixed original physical mesh syntax; classical Hausdorff uniqueness of limits; 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators

theorem AvramDividend.Classical.avram_b28_original_intrinsic_gaussian_unique_physical_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R B : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hBsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω)))
    (σ : Ω → ℝ≥0) (S : Finset ℕ)
    (a b : ℕ → ℝ≥0) (WG : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) =
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (B (b i) ω - B (a i) ω)) := by sorry
