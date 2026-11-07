-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_survival_cash_source_bound
-- name    : AvramDividend.Classical.avram_p3_comp8_original_canonical_survival_cash_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:55:29.249201+00:00
-- url     : https://prove2.me/theorems/60f7c7ef-d662-4a3c-9dcc-6365cb094fe1
-- title:
--   Original prescribed uniform mesh inherits the surviving-path strict cash and physical source inequality
-- statement:
--   The proved P3-GRID4 surviving-path source cash inequality quantifies an existential uniform mesh. Its uniform formula determines every grid point uniquely, so the bound applies directly to the prescribed arbitrary uniform u_n in canonical 4044. The physical source term and final horizon bridge remain exactly as in the proved input; ruin paths require separate treatment.
-- source:
--   Proved fc30bcbb-8850-470e-b746-d6891026e7a4; equality of NNReal grids from exact ℝ coefficients; preserves original D, X, T and stopped cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_survival_physical_source_family_witness
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_canonical_survival_cash_source_bound
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
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n ω, ENNReal.ofReal T < ruinTime X x D ω →
      let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u n i : ℝ)))
      let source : ℕ → ℝ := fun i =>
        V (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
        V (x + X.X (u n i) ω - rightLimit D (u n i) ω)
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) ≤
        w x + (∑ i ∈ Finset.range (n + 1), e i * source i) +
          e (n + 1) *
            (V (x + X.X S ω - rightLimit D (u n (n + 1)) ω) -
              V (x + X.X (u n (n + 1)) ω -
                rightLimit D (u n (n + 1)) ω)) := by sorry
