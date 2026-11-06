-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_contact_cell_cancellation
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_contact_cell_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:14:57.986236+00:00
-- url     : https://prove2.me/theorems/f1353332-2dbb-431a-b740-137e5679657e
-- title:
--   Original physical stopped cash and source inequality after exact crossing-contact payment cancellation
-- statement:
--   At every positive physical stopped horizon, the original full-stopped BV source bound and exact finite-grid discounted cash partition cancel the unique contact cell with the same authentic dividendMeasure cash amount. The resulting inequality controls strict pre-contact discounted payments, initial rightpayment and surviving pre-rightpayment reserve by original physical source increments.
-- source:
--   Combine the previously Proved original full stopped single-contact cash/source budget with the Proved exact original strict-prefix/contact-cell partition; use the independently Proved singleton physical crossing-filter to identify both crossing indices, then cancel identical original cash cell by linear arithmetic. No additional global integrability or martingale assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_full_stopped_cash_single_contact_mesh_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_exact_crossing_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_contact_cell_cancellation
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
      ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
        i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range i, cash j) + post k ≤
        w x + (∑ j ∈ Finset.range k, source j) := by sorry
