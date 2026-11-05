-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_strict_cash_C1_grid_with_cap_correction
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_strict_cash_C1_grid_with_cap_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:41:45.262793+00:00
-- url     : https://prove2.me/theorems/5f66fa7e-3689-4c76-b3fe-46d8d6cec791
-- title:
--   Full original BV strict-open discounted C1 mesh budget with exact above-cap source correction
-- statement:
--   For the actual original spectrally negative bounded-variation Lévy source and admissible physical right-payment control, the full discounted strict-open finite-grid cash plus survivor inequality holds with every genuine negative jump and source C1 Taylor error, the true negative q-clock and time-zero atom, and an additional explicit sum of cap-crossing corrections in frozen source cells. This removes the old cap-safe hVSource premise. The correction must be controlled by smooth-fit/local Taylor under legitimate P3-G compact-strip clocks; no generator compensation, surrogate process, or canonical stopped conclusion is assumed.
-- source:
--   Proved original strict-open P3-C full cash and clock budget 02e2ddd8, physical source error 038f0c69, accepted F6 cap-source crossing 84f8df8a; adaptation of accepted F1 proof 5341265a with no hVSource.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_physical_C1_jump_grid_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_strict_cash_C1_grid_with_cap_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i, i < n → u i ≤ u (i + 1))
    (b : ℝ≥0) (hFinal : u n < b)
    (S : Finset ℕ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      let d : ℕ → ℝ := fun i => X.X (u (i + 1)) ω - X.X (u i) ω
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let B : ℝ := |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0))
      let tail : ℝ := ∑ i ∈ Finset.range n,
        if i ∈ S then |c i| else |j i|
      let κ : ℕ → ℝ := fun i =>
        let p := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
        if C = ⊤ then 0
        else if p ≤ C.toReal then 0
        else w C.toReal + (p - C.toReal) - w p
      let cash : ℕ → ℝ := fun i =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal
      let post : ℕ → ℝ := fun i =>
        V (x + X.X (u i) ω - rightLimit D (u i) ω)
      let finalCash : ℝ :=
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioo (u n : ℝ) (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal
      ∀ (hPre : ∀ i, i < n →
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
        (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω)
        (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
        (htaylor : ∀ i, i < n →
          |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
            ε * |c i|)
        (hlarge : ∀ i, i < n → i ∈ S →
          |w (z i + c i - j i) - w (z i - j i)| ≤ K * |c i| ∧
          |w (z i + c i) - w (z i)| ≤ K * |c i|)
        (hsmall : ∀ i, i < n → i ∉ S →
          |w (z i + c i - j i) - w (z i + c i)| ≤ K * |j i| ∧
          |w (z i - j i) - w (z i)| ≤ K * |j i|),
      rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
        Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
        w x + (∑ i ∈ Finset.range n,
          e i * ((w (z i - j i) - w (z i)) +
            deriv w (z i) * c i)) +
        e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
          V (x + X.X (u n) ω - rightLimit D (u n) ω)) +
        ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) +
        (Real.exp (-(q * (b : ℝ))) - e n) *
          w (riskProcess X x D b ω) +
        ε * B + 2 * K * tail +
        (∑ i ∈ Finset.range n, e i * κ i) := by sorry
