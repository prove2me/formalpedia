-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_discounted_product_source_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_initial_discounted_product_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:27:32.704762+00:00
-- url     : https://prove2.me/theorems/1a7c8151-070a-453e-a028-3d856170eb83
-- title:
--   Original BV full discounted pre-ruin source budget with correct time-zero atom and clock product
-- statement:
--   Under the original positive cap and admissibility, the actual original initial right-dividend atom plus complete once-discounted paymentTimes cash and discounted post-rightpayment w-value is bounded by w(x) plus source-only cap-linear increments discounted at left grid clocks and the exact discrete q-clock correction, on any pre-ruin finite grid beginning at zero. This uses actual X,D,hjump, finite/infinite cap, and correct source-before-payment ordering.
-- source:
--   Original Proved discounted full grid product budget 718dea3e, original time-zero hjump ledger e6bfefd9, and actual postpayment V=w 37425aad. Cash is discounted exactly once.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_initial_discounted_product_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) +
      e n * w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by sorry
