-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
-- name    : AvramDividend.Classical.avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:18:36.688198+00:00
-- url     : https://prove2.me/theorems/c475a4da-6bc1-45de-afb8-fe88fa17e536
-- title:
--   Original controlled compact-band Brownian gradient belongs to predictable L2 class
-- statement:
--   The original pathwise controlled strict-left compact interior reserve gradient, hence the Brownian stochastic integrand up to a fixed Gaussian coefficient, is genuinely MemLp 2 under every finite predictable observation law, in addition to being predictable. Works with arbitrary adapted Stieltjes dividends, whose singular and right-atomic parts are not suppressed.
-- source:
--   Canonical controlled compact interior derivative measurable and finite squared integral bcd9edf0, Mathlib memLp_two_iff_integrable_sq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable)
      _ _ G 2 μ := by
  sorry
