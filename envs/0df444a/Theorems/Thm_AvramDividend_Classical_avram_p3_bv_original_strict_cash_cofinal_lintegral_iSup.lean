-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:53:53.182372+00:00
-- url     : https://prove2.me/theorems/afaa5e7b-f1e9-46a1-8534-077aa11abede
-- title:
--   Original stopped discounted strict cash is the monotone limit of cofinal strict cutoff cash
-- statement:
--   On a fixed genuine original dividend path, the complete discounted Stieltjes cash strictly before T is the supremum of complete cash strictly before a monotone cofinal sequence of earlier cutoffs. The only independent additional hypothesis is measurability of the actual pathwise payment-time restrictions, needed for monotone convergence. This retains every left-payment, right-payment and diffuse payment strictly before T but excludes the atom at T.
-- source:
--   Mathlib lintegral_iSup of measurable increasing ENNReal indicator functions and original paymentTimes/dividendMeasure. Does not assert a stochastic compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n)
    (hMeas : ∀ n, MeasurableSet
      (paymentTimes (ruinTime X x D ω) ∩ Iio (u n))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
