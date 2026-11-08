-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps12_original_random_clock_discounted_Taylor_kernel_L1
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps12_original_random_clock_discounted_Taylor_kernel_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:37:37.150386+00:00
-- url     : https://prove2.me/theorems/3750285a-537f-493d-9d24-063d536fbad8
-- title:
--   Original stopped Lévy discounted Taylor jump kernel integrable under any right-continuous stopping clock
-- statement:
--   In Avram's original spectrally negative Lévy process and original dividend strategy, the stopped discounted generator Taylor jump kernel is integrable under the product of a finite predictable time measure and the actual negative Lévy measure. It is stopped inclusively at any stopping time of the original right-continuous filtration. Follows from verified original-process predictable product integrability and verified predictable stopping-mask measurability; no martingale claim is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_arbitrary_predictable_band_product_Integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps12_original_random_clock_discounted_Taylor_kernel_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
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
    let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then GW p else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable GWσ (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
