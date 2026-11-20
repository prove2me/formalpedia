-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos_topcap_each_grid
-- name    : AvramDividend.Classical.avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos_topcap_each_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:13:25.490362+00:00
-- url     : https://prove2.me/theorems/bf9a40db-c779-4aa8-aaa8-7a922b73aed7
-- title:
--   Original topcap clipped physical-grid discounted source cash sign
-- statement:
--   Original same-process canonical clipped finite grid; exact discounted Ioc Stieltjes cash plus w-potential payment increments is nonpositive for a zero-or-strict pre-ruin clock at top cap. Applies at any negative-jump activity level.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos_topcap_each_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v i : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by sorry
