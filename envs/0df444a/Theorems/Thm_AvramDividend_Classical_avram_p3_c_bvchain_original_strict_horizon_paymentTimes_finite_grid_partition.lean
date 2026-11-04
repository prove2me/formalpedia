-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:36:36.72783+00:00
-- url     : https://prove2.me/theorems/8b976562-985a-4ad0-b157-23ce5e3cfeb1
-- title:
--   Original strict-horizon stopped Stieltjes cash equals all right-closed interior grid cash plus open final cash
-- statement:
--   On the literal original ruin-stopped payment-time set and any strictly increasing finite mesh from zero ending strictly before horizon b, the discounted ENNReal dividend Stieltjes integral over (0,b) is exactly the finite sum of right-closed interior cells plus the open final cell. Physical intermediate right-payment atoms appear once, the zero and terminal right-payment atoms are excluded, and all diffuse dividend mass is preserved without a finite-integral assumption.
-- source:
--   Induction using the public Proved original paymentTimes strict-open two-cell partition 209a3681, with exact Stieltjes lintegral additivity; Avram Proposition 4(i), Equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hgrid : ∀ i, i < n → u i < u (i + 1))
    (b : ℝ≥0) (hfinal : u n < b) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
