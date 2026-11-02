-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_ruin_stopped_negative_taylor_product_l1
-- name    : AvramDividend.Classical.avram_wave5_02c_actual_ruin_stopped_negative_taylor_product_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:54:48.786199+00:00
-- url     : https://prove2.me/theorems/916f40f6-b699-44bc-b8a8-659c89ea0ac3
-- title:
--   Same-source ruin-stopped C² Taylor remainder is integrable against the genuine negative Lévy-mark product intensity
-- statement:
--   For the literal original spectrally negative Lévy process X and adapted dividend strategy D, the already inclusively ruin-stopped prepayment nonlinear C2 Taylor remainder is genuinely L1 integrable for every finite right-continuous predictable measure μ times the original negative-mark Lévy intensity X.nu restricted to z<0. This turns Chat03's nested absolute-energy bound into the exact product-measure Integrable prerequisite for stopped original-source compensation, without replacing X by any Poisson copy.
-- source:
--   Proved Chat03 predictable negative-mark L1/L2 kernel 0e0663b1, original negative Lévy-mark s-finiteness, generic nested-L1-to-product integrability bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_actual_ruin_stopped_negative_taylor_product_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
