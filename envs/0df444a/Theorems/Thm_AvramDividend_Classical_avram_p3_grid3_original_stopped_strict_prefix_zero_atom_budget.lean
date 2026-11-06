-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
-- name    : AvramDividend.Classical.avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:12:18.259856+00:00
-- url     : https://prove2.me/theorems/8eddbe03-6991-4ff1-8f4a-8e2a9854171c
-- title:
--   Genuine original BV stopped physical strict-prefix cash terminal budget including time-zero payment atom
-- statement:
--   For each original ruin-clamped physical prefix ending strictly before the stopped time, the actual admissible D and original Levy X satisfy a weighted finite-grid cash plus terminal and source budget with the literal initial rightLimit D(0) dividend atom. All per-cell pre-ruin and monotonicity assumptions follow from the genuine physical stopping clock. The cap-linear extension and exact canonical rightpayment secant condition handle positive cap contact and zero-time cash. The terminal crossing at ruin remains separate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_weighted_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_stopped_clock_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
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
    (T : ℝ≥0) (m n : ℕ)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r (i + 1))
    (hr0 : r 0 = 1) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u n < τ →
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
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
        r n * post n ≤
      w x + (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by sorry
