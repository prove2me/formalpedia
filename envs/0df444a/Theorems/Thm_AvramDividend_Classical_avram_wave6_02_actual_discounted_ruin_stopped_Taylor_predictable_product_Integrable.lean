-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_Integrable
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_Integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:04:33.759591+00:00
-- url     : https://prove2.me/theorems/fc293da7-cc07-49f5-803f-481a7cc33f56
-- title:
--   Actual discounted ruin-stopped controlled C2 negative-jump Taylor kernel is genuinely integrable on original predictable product measure
-- statement:
--   For the actual spectrally negative Levy process X, dividend strategy D, finite horizon T, discount q≥0 and inclusive ruin stop, the original right-continuous predictable negative-jump Taylor product kernel GW has an ordinary integrable first absolute moment. Unlike L2 alone on an infinite Lévy product measure, this requires the separately Proved absolute L1 Taylor energy. No finite first moment of the small-jump Levy measure is assumed.
-- source:
--   Apply the accepted actual GW MemLp2 theorem to obtain AEStronglyMeasurable GW on the physical right-continuous predictable product. The separately accepted actual GW finite L1 absolute lintegral supplies HasFiniteIntegral after Real.enorm_eq_ofReal_abs. The Integrable constructor then yields genuine Bochner integrability without assuming the product measure finite or an infinite-activity small-jump first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_Integrable
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
      Integrable GW (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
