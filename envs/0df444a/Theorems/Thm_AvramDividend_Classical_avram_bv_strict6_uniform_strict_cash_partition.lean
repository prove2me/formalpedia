-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_uniform_strict_cash_partition
-- name    : AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:09:21.974206+00:00
-- url     : https://prove2.me/theorems/87f2ed3e-d92c-40ad-babf-05baf2c6d518
-- title:
--   Exact original strictly increasing uniform-grid strict cash partition
-- statement:
--   Specialise the Proved original stopped dividendMeasure strict real cash partition to a genuinely uniform physical grid u_i=T*i/(n+2), with last endpoint b=T-T/(n+2). Derive the strict cell inequalities from T>0. The resulting identity uses only open pre-horizon cash on (0,b), n right-closed interior cells, and one open final cell; it neither includes the time-zero atom nor a dividend at b or T. Those atoms are controlled separately in the original verification proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, (u i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (b : ℝ≥0)
    (hb : (b : ℝ) = T - T / ((n : ℝ) + 2)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
