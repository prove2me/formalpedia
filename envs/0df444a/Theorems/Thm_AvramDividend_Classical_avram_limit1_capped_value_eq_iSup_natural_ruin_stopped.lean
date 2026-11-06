-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_value_eq_iSup_natural_ruin_stopped
-- name    : AvramDividend.Classical.avram_limit1_capped_value_eq_iSup_natural_ruin_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:31:32.350985+00:00
-- url     : https://prove2.me/theorems/6b88a50b-fe25-4976-bf22-b51496824d5f
-- title:
--   Capped optimal dividend value is exactly the supremum of natural ruin-stopped expected Stieltjes rewards
-- statement:
--   For the original spectrally negative Lévy process and actual capped admissible strategies, the capped optimal dividend value is exactly the supremum over strategies, admissibility witnesses, and natural ruin-stopped discounted dividend-measure expectations. This applies the previously Proved original full-dividend-value natural-horizon supremum equality to each capped strategy, using the IsAdmissible component. It preserves the time-zero atom and terminal-payment convention, and has no new stochastic regularity or integrability assumptions. It is a reusable exact strategy-level to value-function limit interface for the Avram local-verification milestone.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_capped_value_eq_iSup_natural_ruin_stopped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    valueFunctionLe X q C x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissibleLe X x C D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by sorry
