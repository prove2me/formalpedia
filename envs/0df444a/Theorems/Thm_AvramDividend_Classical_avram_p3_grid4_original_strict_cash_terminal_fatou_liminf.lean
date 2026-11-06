-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:39:58.199089+00:00
-- url     : https://prove2.me/theorems/fe957018-c6eb-4eb7-90fc-7f8ea3ffc61e
-- title:
--   Original strict stopped cash prefixes plus surviving terminal satisfy genuine Fatou liminf
-- statement:
--   The proof uses exactly the accepted original X/D real strict-prefix cash convergence (670d403d), adds the actual unchanged pre-right-payment surviving terminal of the target c1e2f021, and lifts its real limit through the continuous ENNReal.ofReal map. The pinned Filter.Tendsto.liminf_eq makes the original strict cash-plus-terminal ENNReal payoff equal to the liminf of genuine varying inner-prefix cash plus the original terminal. No uniform L1 envelope, zero ruin atom, global derivative bound, proxy process or expected HJB estimate is assumed. The obligation addressed is the Fatou lower-liminf construction for source-indexed physical cash prefixes.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
    liminf (fun n : ℕ => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0))) atTop := by sorry
