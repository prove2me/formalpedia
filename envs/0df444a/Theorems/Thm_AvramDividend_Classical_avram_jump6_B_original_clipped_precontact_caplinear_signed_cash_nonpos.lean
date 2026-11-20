-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos
-- name    : AvramDividend.Classical.avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:15:39.462795+00:00
-- url     : https://prove2.me/theorems/052f4ab6-ff25-4368-a7d8-b0371f65b002
-- title:
--   Canonical clipped grid original caplinear signed discounted cash is nonpositive before ruin
-- statement:
--   For any original spectrally negative Levy path and admissible capped dividend strategy, the canonical time grid clipped at a zero-or-strictly-pre-ruin clock has nonpositive total source-exact discounted cash plus caplinear right-dividend potential increments. This is the fully quantified physical-grid specialization of the Proved original per-grid signed cash theorem. It supports the mixed infinite-activity dividend source without assuming finite negative-jump intensity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos
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
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range m,
      ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v i : ℝ))) *
        (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by sorry
