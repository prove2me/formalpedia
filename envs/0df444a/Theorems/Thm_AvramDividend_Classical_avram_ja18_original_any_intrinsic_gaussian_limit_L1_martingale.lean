-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_any_intrinsic_gaussian_limit_L1_martingale
-- name    : AvramDividend.Classical.avram_ja18_original_any_intrinsic_gaussian_limit_L1_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:50:03.589893+00:00
-- url     : https://prove2.me/theorems/93979425-9a83-4a86-87ca-369e4a8dd155
-- title:
--   Any original intrinsic Gaussian limit representative inherits finite activity L1 martingale law
-- statement:
--   For the genuine original finite-negative-activity Standing Levy source, any process R that is a simultaneous almost-sure limit of the original Gaussian truncated residuals is integrable at every time and is a martingale under the original right-continuous filtration. This removes the extra canonical martingale assumptions currently required by the full negative-jump stopped martingale bridge. It follows from Proved existence of a canonical adapted L1 Gaussian martingale and a.e. uniqueness of limits at each time, then transport of conditional expectations by a.e. equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_any_intrinsic_gaussian_limit_L1_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    (∀ t : ℝ≥0, Integrable (R t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by sorry
