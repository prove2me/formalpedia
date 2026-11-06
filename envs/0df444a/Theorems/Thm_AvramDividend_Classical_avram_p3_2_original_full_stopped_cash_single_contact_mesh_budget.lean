-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_full_stopped_cash_single_contact_mesh_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_full_stopped_cash_single_contact_mesh_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:58:40.3342+00:00
-- url     : https://prove2.me/theorems/f21fda7f-2648-4108-a65d-93bf373fd207
-- title:
--   Original full stopped BV cash with one explicitly vanishing-width contact cell
-- statement:
--   For the authentic spectrally negative Lévy path and admissible dividend strategy, the full stopped discounted dividend cash and pre-rightpayment reserve are bounded by the original physical source increments and exactly one ruin/horizon crossing cash cell. That contact cell has length at most T/(m+1), retaining the initial rightpayment, ruin and cap-contact boundaries.
-- source:
--   Combine accepted GRID4 original full stopped cash with its boundary filter, GRID3 physical positive stopped clock singleton crossing filter, and GRID3 mesh gap theorem. Identify the gap index via the singleton filter and simplify the contact sum to one authentic dividendMeasure cash cell. No circular canonical target, surrogate, axiom, sorry or false martingale zero mean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_full_stopped_cash_single_contact_mesh_budget
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
        τ - u i ≤ T / (m + 1) ∧
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range (m + 1), cash j) + post k ≤
        w x + (∑ j ∈ Finset.range k, source j) + cash i := by sorry
