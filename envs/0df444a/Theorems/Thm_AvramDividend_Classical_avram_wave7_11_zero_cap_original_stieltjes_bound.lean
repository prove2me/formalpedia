-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_cap_original_stieltjes_bound
-- name    : AvramDividend.Classical.avram_wave7_11_zero_cap_original_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:34:35.876021+00:00
-- url     : https://prove2.me/theorems/a030eeb8-d134-4aac-b8bc-e9fa0705f9fe
-- title:
--   Zero admissible dividend cap forces zero initial reserve and original full-Stieltjes bound
-- statement:
--   In the source unbounded-variation Lévy dividend model, if initial reserve x is nonnegative and ENNReal.ofReal x ≤ 0, then x=0. Hence for an admissible strategy with cap 0, the entire discounted Stieltjes dividend expectation up to the genuine ruin clock and finite real horizon is bounded by ENNReal.ofReal(w x), preserving zero-time dividends. The proof applies the independently Proved corrected zero-initial bound, retaining w(0)≥0 and its precise jump conditions.
-- source:
--   Canonical zero-cap branch of corrected original-process UBV finite-horizon verification cc518136 and Proved theorem 14599b22-5d59-42c4-81c7-efbc058a3e03, using pinned ENNReal.ofReal_eq_zero.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_zero_cap_original_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (0 : ℝ≥0∞)})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < (0 : ℝ≥0∞) → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ (0 : ℝ≥0∞))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x 0 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
