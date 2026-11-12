-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
-- name    : AvramDividend.Classical.avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T14:41:13.095263+00:00
-- url     : https://prove2.me/theorems/10ff2b5a-b5c7-406b-8a92-4a375699ac90
-- title:
--   Original measurable Gaussian and bounded-jump components have exact orthogonal square moments
-- statement:
--   On the same probability space and right-continuous filtration as the original finite-activity Lévy process, identify measurable Gaussian and compensated small-band jump functions whose sum equals the intrinsic finite-cutoff residual almost surely, whose squares are integrable, which are orthogonal in expectation, and whose individual second moments equal t sigma squared and the original Lévy second-moment band respectively. The product-integrability consequence is proved separately by the generic square-integrability theorem.
-- source:
--   J-A21 reduction of original finite-cutoff component theorem ebbab4df; complementary generic product-integrability theorem 101dae79 is already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ∃ (G J : Ω → ℝ),
        (∀ᵐ ω ∂P,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = G ω + J ω) ∧
        AEStronglyMeasurable G P ∧
        AEStronglyMeasurable J P ∧
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
