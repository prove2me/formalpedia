-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_surviving_mesh_closed_horizon_cash_source_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_surviving_mesh_closed_horizon_cash_source_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-04T18:06:16.274193+00:00
-- url     : https://prove2.me/theorems/dc214082-2223-4ee1-adb9-efe9fc3f1b36
-- title:
--   Original strict-survival full closed-horizon Stieltjes cash and post-rightpayment terminal source-grid budget
-- statement:
--   On original process sample paths which strictly survive a positive horizon T, the exact closed-horizon Stieltjes cash including the right-payment atom and post-rightpayment discounted terminal value are bounded by initial value plus original source frozen-grid increments and the last source tail. No noncausal stopping, replacement source, or omitted payment atom is introduced. This pathwise branch does not claim the original ruin-crossing case.
-- source:
--   Proved original strict-surviving literal cash grid 8a464b87 and exact original closed-horizon atom accounting d7254588.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_surviving_mesh_full_cash_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Original positive-horizon closed Stieltjes cash, including the right
horizon payment atom, on strictly surviving original paths. This combines
the full frozen-source cash grid with genuine right-atom absorption. -/

theorem AvramDividend.Classical.avram_p3_bv_original_surviving_mesh_closed_horizon_cash_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x)
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
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (u : ℕ → ℝ≥0) (hu : StrictMono u) (n : ℕ) (hzero : u 0 = 0)
    (hFinal : u n < (⟨T, hT⟩ : ℝ≥0)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → Ω → ℝ := fun i ω =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i ω) +
        e n * (V (x + X.X S ω - rightLimit D (u n) ω) -
          V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
