-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_nearzero_smallband_variance_global_statement_false
-- name    : AvramDividend.Classical.avram_ja18_original_nearzero_smallband_variance_global_statement_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:23:19.940688+00:00
-- url     : https://prove2.me/theorems/066a5a87-7c83-4907-9ee2-45eeae07e7af
-- title:
--   Formal negation of incorrect intrinsic smallband complementary-strip universal variance identity
-- statement:
--   The exact type-zero instance of the universally quantified nearzero-band second-moment claim for the original Levy smallband compensated source is mathematically false. The counterexample is an original Standing finite-activity compound-Poisson spectrally negative Levy model with uniform negative marks, whose retained n=0 band is empty and complementary (-1,0) quadratic energy is 1/3. This full negation is implied by the already Proved concrete source counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_nearzero_smallband_variance_global_statement_false :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕)
        (_hX : X.Standing)
        (_hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤),
      ∀ (n : ℕ) (t : ℝ≥0),
        (∫ ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
          (t : ℝ) *
            (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by sorry
