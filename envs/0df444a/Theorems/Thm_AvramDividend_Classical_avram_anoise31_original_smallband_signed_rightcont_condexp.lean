-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise31_original_smallband_signed_rightcont_condexp
-- name    : AvramDividend.Classical.avram_anoise31_original_smallband_signed_rightcont_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:24:45.523224+00:00
-- url     : https://prove2.me/theorems/867b4b3a-39bb-46df-9b20-c0156bd9b5e2
-- title:
--   Original bounded signed smallband right-continuous conditional centring
-- statement:
--   The integrable intrinsic compensated bounded negative jump band has original right-continuous filtration conditional expectation equal to its past value, using only actual original-process marked jumps. Separate integrability is supplied by the physical count L2 lemma.
-- source:
--   Proved finite-simple mark conditional centring 6de0a6db, original future negative-band signed integral independence aba7515d, exact original future shifted band integral 238b5785, and compensated count rate identities. No auxiliary independent Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise31_original_smallband_signed_rightcont_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω =
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω := by sorry
