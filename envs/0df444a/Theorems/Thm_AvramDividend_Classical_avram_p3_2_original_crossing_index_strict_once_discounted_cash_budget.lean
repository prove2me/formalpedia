-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:36:43.371223+00:00
-- url     : https://prove2.me/theorems/4a3a3437-4886-4f12-b625-5f990d1a53b7
-- title:
--   Original BV exact-crossing strict cash and terminal with one discount
-- statement:
--   At the actual ruin/horizon stopped mesh crossing index, the original dividendMeasure strict prefix cash, each atom carrying exactly one discount, plus the original riskProcess pre-rightpayment terminal and initial right payment is bounded by w(x) plus the original finite physical source increments. The remaining crossing gap is at most one mesh cell.
-- source:
--   Compose the already Proved GRID3 original stopped strict-prefix zero-atom source-budget theorem with the already Proved original positive strict crossing mesh-gap theorem, instantiating the arbitrary nonnegative weights by constant one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
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
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range i, cash j) + post i ≤
        w x + (∑ j ∈ Finset.range i, source j) := by sorry
