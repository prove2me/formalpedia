-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
-- name    : AvramDividend.Classical.avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:17:31.355188+00:00
-- url     : https://prove2.me/theorems/ff34b783-f7be-47fc-a982-e911ea66ee35
-- title:
--   Original Gaussian L2 Doob maximal transfer from its finite horizon square moment
-- statement:
--   Prove the source-faithful continuous-time Doob L2 maximal estimate for the intrinsic Gaussian residual of the original finite negative jump activity Lévy process. Given integrability of its true R_n squared terminal value, obtain a single integrable random envelope dominating its entire original sample path over [0,n]. This uses continuous source paths and right-continuous martingale properties and avoids the false assertion that sample-path compact boundedness alone implies integrable supremum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n)
    (hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P) :
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖R t ω‖ ≤ B ω) := by sorry
