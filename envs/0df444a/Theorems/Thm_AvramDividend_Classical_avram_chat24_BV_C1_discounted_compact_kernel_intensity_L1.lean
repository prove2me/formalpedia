-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1
-- name    : AvramDividend.Classical.avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:28:35.425769+00:00
-- url     : https://prove2.me/theorems/210fcd45-948a-4206-af92-08689518da56
-- title:
--   Actual BV C1 discounted compact reserve kernel has finite predictable intensity L1
-- statement:
--   For the actual original bounded-variation Levy X and dividend D, derive predictability of the strict-left reserve and measurable finite marked-intensity L1 of the discounted negative-jump payoff kernel localized to a compact positive reserve band and a deterministic finite horizon. Derive all Lipschitz/value bounds from C1 compact regularity and all Levy tail finiteness from the original source. This statement assumes no jump-occupation integrability, compensation identity or integral convergence. It is the intensity-side analytic component of original stopped occupation regularity parent 434a944f-a6f4-4b64-8aa8-8554ba093a5c.
-- source:
--   Second mathematical split of exact original stopped occupation regularity 434a944f after static size/complexity refusal; reuses Proved original predictable BV marked-product first-moment theorem 221ffdc4 and analytic certificate e61f5d17.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (T : ℝ≥0) (μ : @Measure (ℝ≥0 × Ω) 𝓕.rightCont.predictable) (hμ : μ univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : ℝ≥0 × Ω → ℝ := fun p => if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => A p.1 *
      (if Y p.1 ∈ Icc a b ∧ p.2 < 0 then w (Y p.1 + p.2) - w (Y p.1) else 0)
    Measurable[𝓕.rightCont.predictable] Y ∧
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] G ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  sorry
