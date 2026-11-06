-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:26:41.219874+00:00
-- url     : https://prove2.me/theorems/1e32d3a5-a025-478c-bae7-d84aff48d604
-- title:
--   Original BV discounted stopped cash budget at the exact maximal strict pre-ruin grid prefix
-- statement:
--   At a physical original X/D stopped grid, the discounted cash-plus-postpayment-reserve bound holds at the exact maximal prefix of cells ending strictly before the natural ruin clock, preserving the original time-zero dividend payment.
-- source:
--   Construct the exact maximal strict-prefix index using already-Proved original ruin-stopped strict-prefix terminal and physical clock theorems (c0698d63,d8bba788). Apply the fully Proved original discounted zero-atom source budget (8eddbe03) with genuine positive exponential weights; retain the source proof's equality between the filtered pre-ruin cells and Finset.range k. No canonical Open parent or surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
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
    0 < τ → ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter (fun i => u (i + 1) < τ) = Finset.range k ∧
      u k < τ ∧
      rightLimit D 0 ω +
        (∑ i ∈ Finset.range k, r (i + 1) * cash i) +
        r k * post k ≤
      w x + (∑ i ∈ Finset.range k, r (i + 1) * source i) +
        ∑ i ∈ Finset.range k, (r (i + 1) - r i) * post i := by sorry
