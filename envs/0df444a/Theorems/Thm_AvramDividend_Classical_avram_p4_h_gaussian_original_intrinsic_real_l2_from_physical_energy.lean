-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:39:52.944205+00:00
-- url     : https://prove2.me/theorems/a8001c6c-701b-40af-aaba-8985ecd441dd
-- title:
--   Original intrinsic compensated small-jump real L2 isometry from physical source energy
-- statement:
--   The actual original process X and original P have an integrable squared intrinsic compensated jump difference and its real second moment is bounded by the physical original X.ν finite-band quadratic energy whenever the original physical liminf bound, square measurability and real source band integrability hold. Converts a physical Fatou result to the exact Bochner real L2 inequality P4-H needs, with no unrelated Gaussian or decomposition assumption.
-- source:
--   Pinned Mathlib MeasureTheory.ofReal_integral_eq_lintegral_ofReal, MeasureTheory.hasFiniteIntegral_iff_ofReal and ENNReal.ofReal_le_ofReal_iff; original intrinsic band definition and physical Fatou source bound ad3c237d-7c5c-480d-badc-c83534b45517.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ)
    (hSourceEnergy : IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
           (-(1 / (((max n m : ℕ) : ℝ) + 1)))) X.ν)
    (hSquareAE : AEStronglyMeasurable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P)
    (hPhysicalEnergy :
      (∫⁻ ω, ENNReal.ofReal
        ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P) ≤
        (T : ℝ≥0∞) *
          (∫⁻ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            ENNReal.ofReal (z ^ 2) ∂X.ν)) :
    Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
      (T : ℝ) * (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))), z ^ 2 ∂X.ν) := by sorry
