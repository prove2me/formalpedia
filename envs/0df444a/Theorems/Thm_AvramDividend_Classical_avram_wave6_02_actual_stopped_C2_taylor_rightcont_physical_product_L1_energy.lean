-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:16:57.727377+00:00
-- url     : https://prove2.me/theorems/955eaa85-e55a-47c2-aedb-c3ec81ef2a0f
-- title:
--   Actual original controlled ruin-stopped C² Taylor kernel: finite right-continuous predictable Lévy product L¹ energy
-- statement:
--   On the original spectrally negative Lévy source and original adapted dividend control, the inclusive ruin-stopped full C² Taylor kernel has finite product L¹ energy against any finite right-continuous predictable clock and the actual negative Lévy measure. This gives the precise integrability of the physical compensator without imposing infinite-small-jump first absolute moment, and is the product-level partner of the original product L² energy result.
-- source:
--   Canonical original stopped controlled C² full negative Lévy nested L1 energy 0e0663b1, canonical SFinite negative Lévy measure a9270e22, pinned Mathlib lintegral_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|HS p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by sorry
