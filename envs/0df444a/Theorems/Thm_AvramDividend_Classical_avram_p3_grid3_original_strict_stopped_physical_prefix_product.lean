-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_stopped_physical_prefix_product
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_stopped_physical_prefix_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:12:03.555756+00:00
-- url     : https://prove2.me/theorems/f6458d58-1c52-4fcd-b5c4-90bee0cafe6d
-- title:
--   Actual original stopped physical-grid strict-prefix discounted cash and cap-linear C1 source product
-- statement:
--   For the genuine ruin-clamped physical mesh of the original spectrally-negative Levy X and admissible D, any prefix whose endpoint is strictly before the stopped time automatically has every cell strictly before ruin. The exact discounted paymentTimes/Ioc dividendMeasure plus cap-linear terminal budget then follows without independent per-cell pre-ruin or drift-cap assumptions, preserving finite-cap contact. The one final crossing cell and zero/horizon atoms still require separate treatment.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_full_grid_product_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_stopped_clock_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_stopped_physical_prefix_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u n < τ →
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i =>
      Real.exp (-(q * (u i : ℝ)))
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
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 ≤
      (∑ i ∈ Finset.range n, e i * source i) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by sorry
