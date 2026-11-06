-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:51:40.802276+00:00
-- url     : https://prove2.me/theorems/b6cf60e5-c3c8-4524-84dd-11693089c21d
-- title:
--   Original Lévy strict stopped contact-tail cash converges to zero in the real-valued source representation
-- statement:
--   Under actual original IsDividendStrategy, the proved strict Ioo shrinking contact-tail ENNReal integral limit becomes the exact real-valued toReal contact cash limit. No extra stopping-time or surrogate-process hypotheses; this is pointwise in the original sample path, preparatory to integrable dominated convergence.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
      atTop (𝓝 (0 : ℝ)) := by sorry
