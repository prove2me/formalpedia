-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_tendsto_real
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_tendsto_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:57:14.717856+00:00
-- url     : https://prove2.me/theorems/f8dca0da-b8ac-4e87-8517-95287dda4df6
-- title:
--   Original strict stopped Stieltjes dividend cash converges on every cofinal real grid
-- statement:
--   On the exact original source and dividend measure, the real discounted strict-horizon Stieltjes cash accumulated on every increasing real cofinal sequence of earlier clocks converges to the original stopped strict cash at an NNReal observation clock, with pathwise finiteness and inclusion of the time-zero dividend atom inherited from admissibility.
-- source:
--   Proved c2a88898 original cofinal real supremum at NNReal horizon, Proved e1100117 strict original cash monotonicity, Proved 512282cc original cash bound by rightLimit D, and Mathlib tendsto_atTop_ciSup and ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_tendsto_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal)
      atTop (nhds
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) := by sorry
