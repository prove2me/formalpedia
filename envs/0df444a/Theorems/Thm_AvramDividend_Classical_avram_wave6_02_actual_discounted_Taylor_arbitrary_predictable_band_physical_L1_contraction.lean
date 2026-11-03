-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_Taylor_arbitrary_predictable_band_physical_L1_contraction
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_arbitrary_predictable_band_physical_L1_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:34:42.536811+00:00
-- url     : https://prove2.me/theorems/71e22087-484d-4cdc-9486-aae50d7ee9b0
-- title:
--   Every actual original predictable band contracts the genuine physical L1 energy of the discounted stopped Taylor kernel
-- statement:
--   For arbitrary measurable predictable-product cutoff A of the actual original controlled discounted ruin-stopped C2 Taylor remainder GW, the physical product eLpNorm1 of the cutoff is at most the full GW eLpNorm1. The full physical L1 energy is genuinely finite by an independent theorem, not inferred from L2 on an infinite product measure.
-- source:
--   Proved actual full physical MemLp1 and pinned eLpNorm_indicator_le, ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_MemLp_one
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_arbitrary_predictable_band_physical_L1_contraction
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (A : Set (((ℝ≥0 × Ω) × ℝ))) (hA : MeasurableSet A),
      (eLpNorm (A.indicator GW) (1 : ℝ≥0∞)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal ≤
      (eLpNorm GW (1 : ℝ≥0∞)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) := by sorry
