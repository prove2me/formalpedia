-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_conditional_increment_centred
-- name    : AvramDividend.Classical.avram_ja18_zero_cutoff_conditional_increment_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:00:32.860196+00:00
-- url     : https://prove2.me/theorems/8763ea42-d642-4f30-af47-63534f745e33
-- title:
--   Original zero-cutoff residual has centred future increments
-- statement:
--   Assuming separately established fixed-time L1 integrability, isolate original right-continuous-filtration conditional centring of the zero-cutoff intrinsic residual.
-- source:
--   Exact second conjunct of Open 6bbd3299-8e85-4f09-ab3f-313bc0ed5c4d under its first conjunct as hInt; this is the characteristic exponent and independent-increment accounting obstacle.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_zero_cutoff_conditional_increment_centred
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P) :
    ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω := by sorry
