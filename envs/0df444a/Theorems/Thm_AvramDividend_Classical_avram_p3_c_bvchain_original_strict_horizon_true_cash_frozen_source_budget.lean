-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:32:08.154982+00:00
-- url     : https://prove2.me/theorems/dc8290b6-58e9-4df0-9dc2-4a280df547c4
-- title:
--   Complete original stopped strict-horizon real Stieltjes Cash and prepayment terminal are bounded by frozen Lévy-source increments
-- statement:
--   For the original admissible BV-compatible controlled spectrally negative Levy reserve with strictly increasing finite mesh before ruin, original C1 gradient/boundary/negative extension and actual hjump assumptions, the literal time-zero dividend plus full once-discounted ruin-stopped strict-open (0,b) real Stieltjes dividend Cash and the pre-rightpayment w terminal are bounded solely by actual frozen Lévy-source cap-linear V increments. This is the direct deterministic payout-to-source interface needed by the P3 expected HJB bridge, with no invented stochastic compensation or integrability assumption.
-- source:
--   Proved original strict-horizon clean grid budget 8a24eb9f and source-verified real original exact Stieltjes finite-grid partition; Avram Proposition 4(i), Eq. (5.13).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_clean_strict_horizon_frozen_source_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
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
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
