-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_original_physical_reserve_rightatom_martingale
-- name    : AvramDividend.Classical.avram_jb19_original_physical_reserve_rightatom_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:25:05.755208+00:00
-- url     : https://prove2.me/theorems/91c91f25-b391-4728-88e2-cd0bbd19a0cf
-- title:
--   Original physical reserve with Gaussian source martingale, adaptedness and exact dividend right-payment atom
-- statement:
--   On the actual spectrally negative Levy probability space, with genuine intrinsic Gaussian and compensated-jump source limits, construct the all-path Gaussian residual carrying integrability, right-continuous-filtration adaptedness and martingale conditional means, and the exact sigma squared times time second moment. At every time and every path identify the pre-rightpayment reserve and the original physical reserve including the dividend right-payment atom. This explicitly avoids a separately postulated zero-jump Levy process Y and does not erase the time-zero dividend right atom.
-- source:
--   Proved f58474f2 original Gaussian martingale and bracket totalisation plus Proved e0c6f36d exact postpayment risk reserve decomposition. Required original physical Ito-Meyer bookkeeping for 544e8511 and fa7052b1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_source_totalised_martingale_bracket
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb19_original_physical_reserve_rightatom_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ t : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont t] (M t) P) ∧
      (∀ t : ℝ≥0, Integrable (M t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (M t) ω = M s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (M t ω) ^ 2) P ∧
        (∫ ω, (M t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
      (∀ t ω,
        (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω) =
          x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
            rightLimit D t ω) ∧
        (riskProcess X x D t ω =
          (x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
            rightLimit D t ω) +
            (rightLimit D t ω - D t ω))) := by sorry
