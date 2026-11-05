-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:03:25.527308+00:00
-- url     : https://prove2.me/theorems/639a9479-f8c4-4822-af2e-6506191b254e
-- title:
--   Literal original P3 stopped strict-horizon Stieltjes Cash and pre-rightpayment terminal source-frozen grid budget
-- statement:
--   For the actual original source process and original admissible control on any strictly pre-ruin finite sample grid, the P3 canonical literal real discount Stieltjes cash on paymentTimes(ruinTime) ∩ Iio b plus its strictly pre-rightpayment terminal value is bounded above by w(initial capital) and solely frozen original Levy source V increments. The time-zero right atom is included inside the single literal cash integral, while the horizon right atom is excluded. This is exactly the expected HJB branch's pathwise payoff interface, without postulating the stochastic compensation result.
-- source:
--   Direct accepted original full cash source budget dc8290b6 and source-exact original strict zero-plus-open real partition d58a7561 (pending proof).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i < u (i + 1))
    (hPre : ∀ i : ℕ, i < n → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
