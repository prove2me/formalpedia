-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:20.291981+00:00
-- url     : https://prove2.me/theorems/e0170ed2-0381-462b-899f-112fd4194071
-- title:
--   Original any-cap strict stopped canonical physical-grid caplinear signed cash budget
-- statement:
--   The genuine original spectrally negative Levy reserve and admissible dividends, any positive finite or infinite cap, actual stopping clock t strictly before ruin, canonical stopped physical mesh and exact paymentTimes closed-Iic paid cash satisfy at every grid level: cash plus the original signed initial caplinear V correction minus the true sum of discounted pre/postpayment caplinear V drops is bounded by the actual vanishing real ENNReal mesh error. Reuses original full Stieltjes integral, proven all-cap initial and physical cell signs, and real cash conversion; preserves infinite negative-jump activity compatibility and nonzero Gaussian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_initial_caplinear_postvalue_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_canonical_clipped_cell_V_drop_nonnegative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    let Err : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))
    ∀ j, Cash.toReal + (V (x - rightLimit D 0 ω) - V x) -
      (∑ i ∈ Finset.range (m j),
        Real.exp (-(q * (v j (i + 1) : ℝ))) *
        (V (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
          V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)))
      ≤ (Err j).toReal := by sorry
