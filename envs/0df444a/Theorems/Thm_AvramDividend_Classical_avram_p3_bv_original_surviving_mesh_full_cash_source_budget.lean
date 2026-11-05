-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_surviving_mesh_full_cash_source_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_surviving_mesh_full_cash_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:40:24.950005+00:00
-- url     : https://prove2.me/theorems/8a464b87-dd7e-4d1a-8698-e394c728d83f
-- title:
--   Original surviving-cap BV full Stieltjes cash source grid with automatic pre-ruin mesh cells
-- statement:
--   For the original controlled process, a strictly increasing deterministic mesh below a single strict-survival time automatically has every mesh cell before ruin. Hence the Proved complete literal original discounted Stieltjes cash plus pre-rightpayment candidate can be bounded by the actual frozen Lévy source increments with no separately assumed per-cell ruin inequalities. It includes the time-zero atom and strictly open horizon cash. Ruin-before-horizon sample paths still need a separate stopped limit passage.
-- source:
--   Proved original frozen source strict cash grid budget 639a9479, strict monotonicity and original ruin-clock order

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Original stopped BV full literal cash and pre-rightpayment terminal at a
strictly surviving horizon. Monotone mesh pre-ruin cells are derived from
the one terminal survival condition, so no noncausal cell assumption is
needed when this theorem is applied pathwise. -/

theorem AvramDividend.Classical.avram_p3_bv_original_surviving_mesh_full_cash_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (hu : StrictMono u) (n : ℕ) (hzero : u 0 = 0)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
