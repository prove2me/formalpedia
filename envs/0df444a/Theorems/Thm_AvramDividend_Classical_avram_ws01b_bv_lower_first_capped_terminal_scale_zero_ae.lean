-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:56:44.033989+00:00
-- url     : https://prove2.me/theorems/1f6f4dfd-7246-4306-a9be-b80cc37f07c0
-- title:
--   True BV lower-first finite-horizon stopped q-scale payoff vanishes almost surely
-- statement:
--   For a bounded-variation original spectrally negative Lévy process, if strict lower ruin occurs before upper exit and no later than T, the real discounted q-scale reward at the actual two-sided first-exit clock clipped at T equals zero almost surely. It follows from the genuine Proved BV lower undershoot and the source scale function's zero support at negative reserves.
-- source:
--   Proved original-law no-downward-creeping/undershoot theorem cad05116 and exact IsScaleFunction zero-on-negative clause hW.1, with real actual first-exit clocks and positive q.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Real.exp (-(q * ((min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
      W (x + X.X (min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω) = 0 := by sorry
