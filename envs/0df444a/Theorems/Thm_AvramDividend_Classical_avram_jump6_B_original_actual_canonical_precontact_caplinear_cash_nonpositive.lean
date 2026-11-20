-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_actual_canonical_precontact_caplinear_cash_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_B_original_actual_canonical_precontact_caplinear_cash_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:10:06.557182+00:00
-- url     : https://prove2.me/theorems/993fb5d1-0719-4692-96c5-151fed156460
-- title:
--   Original pre-ruin canonical stopped grid cap-linear signed dividend budget
-- statement:
--   For the genuine original risk process and dividendMeasure, the mesh of positive pre-ruin times up to an arbitrary subordinate clock has nonpositive discounted cash plus cap-linearly extended potential drops. The cap-linear extension preserves the reward inequality above a finite dividend cap and avoids unconstrained w-values there. No finite jump-activity premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_actual_canonical_precontact_caplinear_cash_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
      ((∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (v i : ℝ))) *
          (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
           V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by sorry
