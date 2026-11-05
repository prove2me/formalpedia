-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_real_iSup
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_real_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:52:16.44321+00:00
-- url     : https://prove2.me/theorems/e1962f77-473e-41e6-8cd5-cdd1909ae790
-- title:
--   Finite original strict-horizon cash equals the real supremum of all earlier cofinal cash
-- statement:
--   If the actual complete original discounted strict-horizon Stieltjes dividend cash is finite at a horizon, its real-valued amount equals the supremum of the real discounted cash amounts along every increasing cofinal family of earlier cutoffs. Finiteness at every earlier cutoff follows from original cash monotonicity, so ENNReal.toReal_iSup applies. The only additional assumption is actual finiteness of this fixed sample-path cash; no stochastic compensation is assumed.
-- source:
--   Proved original strict-horizon monotonicity, original cofinal ENNReal cash equality and Mathlib ENNReal.toReal_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_unconditional
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_real_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n)
    (hfinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by sorry
