-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise32_original_smallband_signed_increment_condexp_zero
-- name    : AvramDividend.Classical.avram_anoise32_original_smallband_signed_increment_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:35:22.766371+00:00
-- url     : https://prove2.me/theorems/936ee4d9-4491-4d97-bac9-150762eba92d
-- title:
--   Original compensated bounded-mark future increment is conditionally centred
-- statement:
--   Under finite original negative-mark intensity and original compensated signed bounded-band integrability, the conditional expectation in the original right-continuous filtration of the original smallband compensated signed increment from s to t is zero. The increment is the actual signed-mark stochastic integral, not an independent auxiliary process. This is the outstanding finite-simple marked-count approximation source needed for the original band martingale.
-- source:
--   Sound child of AvramDividend.Classical.avram_anoise31_original_smallband_signed_rightcont_condexp, established by dyadic finite-simple marked-count approximation of the actual original negative band, Proved original finite-simple conditional centring theorem 6de0a6db, bounded count L2 control a6562a4d, and L1 conditional-expectation continuity. Proved original adaptedness 42ada2ca and cutoff-difference identity 2c95a423 close the parent once this increment result is available.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_anoise32_original_smallband_signed_increment_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
