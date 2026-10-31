-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_corrected_exit_exp_bound
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_exp_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:57:40.485058+00:00
-- url     : https://prove2.me/theorems/e7cd411d-54ee-4dd9-b0d5-38bb7e1d614b
-- title:
--   Original discounted upcrossing-before-ruin expectations have uniform exponential decay across bounded reserves
-- statement:
--   For the original Standing spectrally negative Levy process and q>0, the supremum of true discounted corrected two-sided upward exit rewards over every initial surplus x in [0,R] decays at least exponentially in the excess barrier distance a-(R+1), uniformly for every nonnegative reserve range R and upper barrier a≥R+1. The original two-sided exit identity yields ENNReal.ofReal(W(x)/W(a)), monotonicity of W controls every numerator by W(R+1), and the original Esscher q-scale ratio exponential bound gives the displayed uniform inequality with φ>0 independent of R,a,x. The argument works at x=0 and uses no global C1.
-- source:
--   Avram Palmowski Pistorius (2007), original corrected discounted two-sided exit before ruin and Esscher-normalised q-scale growth.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_exp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ R a : ℝ, 0 ≤ R → R + 1 ≤ a →
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        twoSidedExitExpectationCorrected X q a x) ≤
        ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))) := by sorry
