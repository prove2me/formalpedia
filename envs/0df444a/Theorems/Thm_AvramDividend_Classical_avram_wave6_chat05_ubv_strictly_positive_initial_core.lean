-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_ubv_strictly_positive_initial_core
-- name    : AvramDividend.Classical.avram_wave6_chat05_ubv_strictly_positive_initial_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T10:34:24.674839+00:00
-- url     : https://prove2.me/theorems/5dfefcd2-8b97-415b-aebd-4ad77dcd29cb
-- title:
--   Corrected UBV original stopped verification reduced to strictly positive starting reserve
-- statement:
--   This is the genuine strictly positive starting reserve and positive cap branch of the corrected original-process UBV stochastic verification core. The zero starting reserve branch is already Proved by avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound, while nonnegative initial capital follows from admissibility. For x>0 the cap is automatically positive; the remaining conclusion is the authentic expected discounted full Stieltjes dividend inequality, requiring a source-specific controlled Ito-Meyer and martingale localisation argument. No model, cash reward, or HJB hypothesis is changed.
-- source:
--   Derived by exact case split on initial capital in authoritative corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706. Proved original-source theorem b3117b07-8383-4143-a965-2d9876a04a99 gives 0≤x; theorem 14599b22-5d59-42c4-81c7-efbc058a3e03 closes x=0. This isolates the strictly positive initial reserve case. The parent bridge requires a separate guarded proof submission and no graph edge is asserted by publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat05_ubv_strictly_positive_initial_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
