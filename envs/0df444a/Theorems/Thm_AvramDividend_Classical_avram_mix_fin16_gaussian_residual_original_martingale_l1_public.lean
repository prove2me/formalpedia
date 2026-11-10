-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_martingale_l1_public
-- name    : AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_martingale_l1_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:08:26.741231+00:00
-- url     : https://prove2.me/theorems/08823aa3-2669-4a6d-9fd9-99b4f07e72c4
-- title:
--   Original same-filtration intrinsic Gaussian residual is an integrable martingale
-- statement:
--   Derive L1 integrability and original right-continuous filtration conditional martingale law of the source-exact truncated residual limit, reusing the compact-uniform AE field and finite-band compensation. No detached Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_martingale_l1_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    (∀ t : ℝ≥0, Integrable (R t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by sorry
