-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_weighted_source_product_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_weighted_source_product_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:38:47.554859+00:00
-- url     : https://prove2.me/theorems/837277c5-396c-415b-9471-446c7172cf61
-- title:
--   Original BV weighted finite-grid product rule with full stopped Stieltjes cash and frozen source
-- statement:
--   For actual original spectrally negative Lévy X, original admissible left-continuous right-payment strategy D, finite pre-ruin time grid and arbitrary nonnegative step weights, the weighted full dividendMeasure cash and physical postpayment C1 value telescope into weighted source-only cap-linear increments and an exact discrete discount product correction. This exposes the original stochastic residual to P3-A/B, retains right endpoints, diffuse and singular-continuous dividends, and preserves the strict pre-ruin condition.
-- source:
--   Algebraic finite-grid integration-by-parts of the independently Proved original full Stieltjes cell source split, 01e98b05-5e10-44d1-9de2-0050ad1efa47. No unproved stochastic hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_weighted_source_product_budget
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r (i + 1)) :
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
      r n * post n - r 0 * post 0 ≤
      (∑ i ∈ Finset.range n, r (i + 1) * source i) +
      ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by sorry
