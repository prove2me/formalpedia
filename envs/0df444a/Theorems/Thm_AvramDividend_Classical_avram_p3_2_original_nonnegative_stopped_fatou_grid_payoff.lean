-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
-- name    : AvramDividend.Classical.avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:00:29.879645+00:00
-- url     : https://prove2.me/theorems/34f2905e-9c30-4166-828c-71822557e7eb
-- title:
--   Original BV strictly stopped finite-grid physical payoff nonnegative and source bounded
-- statement:
--   The physical original spectrally negative Lévy, capped-admissible dividend-strategy finite-grid strict cash prefix and postpayment w reserve at the precise ruin/horizon crossing index form a nonnegative real payoff and are pathwise bounded by the original physical source increments plus w(x), including the initial right payment. The crossing gap is at most one mesh cell.
-- source:
--   Use fully accepted original strict crossing budget 4a3a3437. Each dividendMeasure ENNReal-to-real cash cell is nonnegative; the previously Proved original capped BV postpayment terminal candidate 28b04520 is nonnegative from w(0)≥0 and the gradient/continuity hypotheses. Sum their signs while retaining the exact source inequality and crossing index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
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
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        τ - u i ≤ T / (m + 1) ∧
        0 ≤ (∑ j ∈ Finset.range i, cash j) + post i ∧
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range i, cash j) + post i ≤
          w x + (∑ j ∈ Finset.range i, source j) := by sorry
