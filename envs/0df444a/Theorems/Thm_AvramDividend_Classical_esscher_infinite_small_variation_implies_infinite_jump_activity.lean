-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_infinite_small_variation_implies_infinite_jump_activity
-- name    : AvramDividend.Classical.esscher_infinite_small_variation_implies_infinite_jump_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:22:47.949739+00:00
-- url     : https://prove2.me/theorems/5e9db1d7-9dc0-45b6-a40c-d2115a4ee205
-- title:
--   Nonnegative Esscher tilts preserve infinite negative jump activity in the infinite-variation small-jump case
-- statement:
--   If the original signed-jump measure has an infinite small-negative-jump absolute first moment, every nonnegative exponential Esscher tilt retains infinite total intensity of negative jumps. The already Proved Esscher first-moment invariance establishes divergence of the tilted first variation; the new Proved measure lemma converts that to infinite tilted negative jump activity. This is the missing direct bridge between the zero-Gaussian unbounded-variation stochastic case and the Esscher tilted excursion Poisson programme.
-- source:
--   Proved esscher_preserves_infinite_small_jump_moment [31e62f85-cfb8-4491-a399-8ca1628d395f], infinite_small_jump_moment_implies_infinite_negative_activity [9c9ba7fd-60ec-487e-a39d-401151963146] candidate 16130. Root-connected Open excursion representation [49acdc06-9a71-482c-b742-ff432e034677].

import Theorems.Thm_AvramDividend_Classical_esscher_preserves_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_implies_infinite_negative_activity
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_infinite_small_variation_implies_infinite_jump_activity
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν) = ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (0 : ℝ)) = ⊤ := by sorry
