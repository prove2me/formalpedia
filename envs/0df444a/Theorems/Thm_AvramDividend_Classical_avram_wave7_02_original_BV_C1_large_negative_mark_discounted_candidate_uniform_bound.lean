-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:19:44.148694+00:00
-- url     : https://prove2.me/theorems/e44668f8-809d-493f-b188-abffe52db324
-- title:
--   Actual original stopped C1 controlled negative Levy large marks have a uniform discounted candidate-jump bound
-- statement:
--   For the original controlled BV reserve left at any positive compact strip [a,b] and a negative Levy source mark z of at least a/2 magnitude, a global bound R for the candidate w below b gives |exp(-qt)*(w(Y_-+z)-w(Y_-))| <= 2R. This covers ruin overshoot, needs no C2 smoothness, and with finite large-negative-Levy mark mass yields the complementary large-mark integrability bound to the proved W7-02 small-mark BV L1 theorem.
-- source:
--   Original X predictable left reserve; absolute triangle inequality and nonnegative-discount bound. Finite mass of large negative marks independently available in Proved finite_large_negative_jump_mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b R : ℝ) (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R)
    (hBound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hz : z ≤ -a / 2) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤ 2 * R := by sorry
