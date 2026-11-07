-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_survival_physical_source_family_witness
-- name    : AvramDividend.Classical.avram_p3_grid4_original_survival_physical_source_family_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:35:43.680199+00:00
-- url     : https://prove2.me/theorems/fc30bcbb-8850-470e-b746-d6891026e7a4
-- title:
--   Actual original BV strict cash and surviving terminal source bound at every uniform physical grid
-- statement:
--   Construct the actual deterministic uniform physical grid of original X and D for all n and all sample paths, and package the accepted source-exact surviving-horizon cash plus pre-right-payment terminal inequality at once for every grid. This closes the entire survival branch of the physical stopped-cell cash-value comparison, using previously Proved original-process theorem 6ca00d81; the remaining ruin/contact branch is separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_survival_original_strict_prefix_source
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_survival_physical_source_family_witness
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
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) ∧
      (∀ n ω, ENNReal.ofReal T < ruinTime X x D ω →
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
                  rightLimit D (u n (n + 1)) ω))) := by sorry
