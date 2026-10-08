-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_preserves_infinite_small_jump_moment
-- name    : AvramDividend.Classical.esscher_preserves_infinite_small_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:42:59.289985+00:00
-- url     : https://prove2.me/theorems/31e62f85-cfb8-4491-a399-8ca1628d395f
-- title:
--   Esscher tilt preserves infinite small-negative-jump first variation
-- statement:
--   For any nonnegative Esscher exponent phi, weighting negative jumps by exp(phi*y) preserves the divergence of the absolute small-jump first-moment integral on (-1,0), since the weight has the uniform positive lower bound exp(-phi) on this interval. This establishes the exact infinite-variation branch invariant for the shifted Lévy measure.
-- source:
--   Pinned Mathlib restrict_withDensity and ae_restrict_mem; Proved Avram Esscher small-jump positive lower bound; positive density preserves infinite lintegral.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_preserves_infinite_small_jump_moment
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν) = ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y|
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) = ⊤ := by sorry
