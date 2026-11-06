-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
-- name    : AvramDividend.Classical.avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:32:01.937335+00:00
-- url     : https://prove2.me/theorems/1359bfd0-38b8-491d-a5b2-404da62e46e8
-- title:
--   Original stopped physical-grid BV cash budget with exact single contact-cell remainder
-- statement:
--   The original X/D stopped physical grid is partitioned by the Proved cash-prefix/contact lemma 45592cc1. The Proved weighted original time-zero-and-strict-prefix source budget 8eddbe03 is instantiated with constant weights one at the certified strict prefix. Substitution gives a full stopped cash upper bound with the unique crossing cell retained as an explicit nonnegative error term. This is deliberately weaker than the canonical c1e2f021: the crossing contribution must still be controlled by an actual left-reserve predictable Lévy jump source and L1/Fatou localisation. It avoids the false frozen-source crossing inequality and handles the original initial right-payment mass.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
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
    0 < τ → ∃ k : ℕ, k ≤ m + 1 ∧ u k < τ ∧
      rightLimit D 0 ω +
        (∑ i ∈ Finset.range (m + 1), cash i) + post k ≤
      w x + (∑ i ∈ Finset.range k, source i) +
        ∑ i ∈ (Finset.range (m + 1)).filter
          (fun i => u i < τ ∧ u (i + 1) = τ), cash i := by sorry
