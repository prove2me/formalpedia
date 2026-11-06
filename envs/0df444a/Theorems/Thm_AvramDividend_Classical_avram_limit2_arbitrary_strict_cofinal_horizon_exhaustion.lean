-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
-- name    : AvramDividend.Classical.avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:57:48.084205+00:00
-- url     : https://prove2.me/theorems/8680a9bd-9ef1-44c5-a386-a7e679d302e7
-- title:
--   Original dividendValue equals supremum of strict Stieltjes cash over every strictly cofinal real horizon schedule
-- statement:
--   Every strictly cofinal deterministic family of real positive/open horizon cutoffs T:ℕ→ℝ exhausts the genuine original full dividendValue through expected discounted Stieltjes cash on paymentTimes(ruinTime) intersect Iio(T k). No monotonicity is needed: for each integer n a later strict T(k)>n includes its closed-horizon cash including the endpoint atom, and for each T(k) an integer n>T(k) dominates the open horizon. Original local and outer lintegral monotonicity sandwich the suprema; no terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a < T k) :
    dividendValue X q x D =
      ⨆ k : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by sorry
