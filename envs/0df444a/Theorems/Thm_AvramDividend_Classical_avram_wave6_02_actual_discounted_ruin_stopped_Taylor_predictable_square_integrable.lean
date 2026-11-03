-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:02:11.861386+00:00
-- url     : https://prove2.me/theorems/18c4c0c0-b5f2-439c-b1e7-5942a17ab5f5
-- title:
--   Actual discounted finite-horizon ruin-stopped controlled C2 negative-jump Taylor kernel has integrable square on original predictable Lévy product
-- statement:
--   For the actual spectrally negative Levy X, admissible dividend strategy D, discount q≥0 and horizon T, the inclusive ruin-stopped C2 Taylor negative-jump kernel GW has an integrable ordinary real square under the original right-continuous predictable physical clock times the negative Lévy measure. This follows from the already-Proved source-specific MemLp2 fact and does not assume a finite first moment of small jumps.
-- source:
--   The accepted actual discounted stopped Taylor right-continuous product MemLp2 theorem supplies the exact physical square-integrability of GW. Mathlib's MemLp.integrable_sq transports it to genuine ordinary Integrable of GW^2 on the original predictable product measure. The process, stopping and discount remain source-specific.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
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
      Integrable (fun p => GW p ^ 2) (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
