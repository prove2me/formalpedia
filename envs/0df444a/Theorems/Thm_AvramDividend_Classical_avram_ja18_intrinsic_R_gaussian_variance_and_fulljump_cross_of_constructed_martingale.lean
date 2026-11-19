-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_R_gaussian_variance_and_fulljump_cross_of_constructed_martingale
-- name    : AvramDividend.Classical.avram_ja18_intrinsic_R_gaussian_variance_and_fulljump_cross_of_constructed_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T14:58:43.338816+00:00
-- url     : https://prove2.me/theorems/153e2b3d-8a35-4e65-997b-1a94b90fd061
-- title:
--   Same-Lévy finite-activity Gaussian intrinsic martingale square bracket and full-jump cross
-- statement:
--   Given the actual finite-activity Levy source intrinsic Gaussian R with almost sure truncated-residual limit, right-continuous adaptedness, integrability, and martingale conditional expectations, prove the original same-source Gaussian variance (integral R(t)^2=t sigma^2) and the L1 orthogonality of Gaussian increments against the full remaining Levy increment X-X-R. The full remaining increment includes negative marks of all sizes. This is the outstanding quantitative same-X bridge, separated from the already-Proved Gaussian source construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18_intrinsic_R_gaussian_variance_and_fulljump_cross_of_constructed_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    (∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      let cross : Ω → ℝ := fun ω =>
        (R t ω - R s ω) *
          ((X.X t ω - X.X s ω) - (R t ω - R s ω))
      Integrable cross P ∧ (∫ ω, cross ω ∂P) = 0) := by sorry
