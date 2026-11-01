-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_legacy_ubv_bound_false_type0
-- name    : AvramDividend.Classical.avram_wave4_p2_legacy_ubv_bound_false_type0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:25:58.673443+00:00
-- url     : https://prove2.me/theorems/be774785-4f12-4eed-9c85-caab60bb3eb9
-- title:
--   The legacy UBV stochastic-bound wrapper is false without the zero-boundary hypothesis
-- statement:
--   The old all-quantified unbounded-variation dividend stochastic-bound wrapper f5cc2d5c-9551-4859-adbb-b39fe0cc7414 is false even when restricted to Type-0 source path spaces. The accepted unconditional Gaussian counterexample to the stronger original core (520139dd-2607-40fc-8888-ecd422d4ebc7), which also assumed an initial cap bound and right-payment secant inequality, immediately refutes this weaker wrapper by discarding those extra hypotheses. This is a diagnostic refutation, not the corrected original-process Itô–Meyer bound; the corrected theorem must retain 0≤w(0) and the genuine Stieltjes/right-payment conditions.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), essential w(0)≥0; accepted Gaussian core negation 520139dd-2607-40fc-8888-ecd422d4ebc7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_ubv_core_false_type0

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_p2_legacy_ubv_bound_false_type0 :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
        (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 2 w
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          1 ≤ deriv w y)
        (x : ℝ)
        (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
        (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω))
        (T : ℝ) (hT : 0 ≤ T),
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) := by sorry
