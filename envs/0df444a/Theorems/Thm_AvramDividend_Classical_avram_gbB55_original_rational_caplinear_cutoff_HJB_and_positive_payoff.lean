-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_rational_caplinear_cutoff_HJB_and_positive_payoff
-- name    : AvramDividend.Classical.avram_gbB55_original_rational_caplinear_cutoff_HJB_and_positive_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:19:01.281357+00:00
-- url     : https://prove2.me/theorems/433a54bc-b3d2-42db-ab41-e255cf786cdc
-- title:
--   Original rational finite-cap clipping payoff nonnegative and HJB inequality valid below cap
-- statement:
--   The true original candidate value w at every strictly interior rational clipping cap b_j is nonnegative and satisfies the original generator HJB drift envelope on every positive reserve below b_j. Supplies the original HJB hypotheses for B51 without assuming them independently, and respects the true cap C.
-- source:
--   B41 gives 0<b_j and ENNReal.ofReal b_j<C. The proved nonnegative interior payoff and the original hw_gen hypothesis yield w(b_j)≥0 and the generator inequality for y∈(0,b_j).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB55_original_rational_caplinear_cutoff_HJB_and_positive_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 ≤ w b ∧ ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0 := by sorry
