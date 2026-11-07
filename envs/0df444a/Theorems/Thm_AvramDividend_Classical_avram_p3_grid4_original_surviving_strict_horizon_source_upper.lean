-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_surviving_strict_horizon_source_upper
-- name    : AvramDividend.Classical.avram_p3_grid4_original_surviving_strict_horizon_source_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:08:01.573676+00:00
-- url     : https://prove2.me/theorems/facfb545-2db8-4937-988a-141b95a004d3
-- title:
--   Original strict surviving horizon source budget with physical-grid upper bound automatically before ruin
-- statement:
--   For genuine original spectrally negative Levy X.X and admissible dividend strategy D, a deterministic strictly increasing physical grid below an actual surviving horizon T yields the exact strict discounted dividendMeasure cash plus pre-right-payment surviving terminal bounded by the accepted cap-linear frozen-X source increments. The per-cell pre-ruin requirement is discharged by the original survival event and each upper grid point ≤ T. This isolates the genuine survival case of the source witness without introducing a proxy process or losing the initial right-payment atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_survival_caplinear_source_mesh
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_surviving_strict_horizon_source_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
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
    (T : ℝ≥0) (hT : 0 < T)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i < u (i + 1))
    (hUpper : ∀ i : ℕ, i < n → u (i + 1) ≤ T)
    (hFinal : u n < T)
    (hSurvive : (T : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (T : ℝ))) * w (riskProcess X x D T ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
        e n * (V (x + X.X T ω - rightLimit D (u n) ω) -
          V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by sorry
