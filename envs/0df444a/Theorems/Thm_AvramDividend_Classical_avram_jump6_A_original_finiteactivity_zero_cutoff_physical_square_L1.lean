-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
-- name    : AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:50:43.973983+00:00
-- url     : https://prove2.me/theorems/c7a69857-93f9-403e-9ac8-2452f2f630c3
-- title:
--   Actual finite-activity Gaussian zero-cutoff residual has square-integrable physical value
-- statement:
--   Establish square integrability of the actual original Gaussian residual after exactly removing the finite-activity negative marks and compensator at zero cutoff, using the original spectrally negative Levy source and its own filtration. This single physical second-moment statement is sufficient with existing proved residual L2 error and maximal martingale results to obtain original bounded-horizon Gaussian L1 supremum without full exact variance identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P := by sorry
