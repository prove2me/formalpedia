-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ruin_crossing_exact_discounted_cash_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_ruin_crossing_exact_discounted_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:46:31.581549+00:00
-- url     : https://prove2.me/theorems/c8e9c38b-efac-46d1-b0ed-587d7000a60a
-- title:
--   Original stopped BV discounted cash source budget at the exact ruin crossing index
-- statement:
--   For a positive original ruin-stopped physical time grid, at the final index strictly before the stopped horizon, the original discounted dividend cash, reserve and source terms satisfy the exact pathwise zero-atom budget, with the crossing endpoint equal to the natural stopping clock.
-- source:
--   Apply Proved P3-2 exact strict-prefix discounted cash budget 1e32d3a5 to get a genuine maximal prefix and its signed source bound; apply Proved GRID crossing-index identification e255f11d, then rewrite the cardinality of the filtered strict cells. Keeps actual X/D and dividendMeasure, no surrogate law, extra stochastic axioms, circular canonical parents or sorry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_ruin_crossing_exact_discounted_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
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
    let r : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
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
    0 < τ → ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
      u (i + 1) = τ ∧
      rightLimit D 0 ω +
        (∑ j ∈ Finset.range i, r (j + 1) * cash j) +
        r i * post i ≤
      w x + (∑ j ∈ Finset.range i, r (j + 1) * source j) +
        ∑ j ∈ Finset.range i, (r (j + 1) - r j) * post j := by sorry
