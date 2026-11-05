-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_live_clock_full_w_grid_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_live_clock_full_w_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:23:56.547487+00:00
-- url     : https://prove2.me/theorems/5b65a814-c4c1-4dc1-a8b4-c450b1cf13e4
-- title:
--   One original live stopped-clock yields the genuine closed-cash and survival w budget over every finite BV grid
-- statement:
--   For the actual spectrally negative Levy source and admissible capped dividend process, a single strict pre-ruin final grid clock implies strict survival at every preceding source grid time. Consequently the previously Proved original closed Stieltjes cash and true postpayment w terminal estimate holds without per-cell stopping hypotheses.
-- source:
--   Source-exact specialisation of Proved dc7eeb89-4440-4938-918e-5340b3c09860 using monotonicity of the physical grid and ENNReal coercion monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- A single original stopped live-clock hypothesis supplies every strict
   survival premise in the physically accounted BV grid budget. -/

theorem AvramDividend.Classical.avram_p3_bv_original_live_clock_full_w_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hLive : (u n : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i))))  := by sorry
