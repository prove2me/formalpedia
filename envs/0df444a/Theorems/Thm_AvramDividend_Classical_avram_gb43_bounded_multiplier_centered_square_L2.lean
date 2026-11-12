-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb43_bounded_multiplier_centered_square_L2
-- name    : AvramDividend.Classical.avram_gb43_bounded_multiplier_centered_square_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:36:06.851466+00:00
-- url     : https://prove2.me/theorems/17550800-cd49-4253-becc-327993f8dd5d
-- title:
--   Bounded multipliers preserve integrable centred-square second moments
-- statement:
--   On a probability space, if R squared is integrable and its expectation is at most B, and H is a measurable function bounded in absolute value by a nonnegative constant K, then (H times R) squared is integrable and its expectation is at most K squared times B. The result applies directly to the original finite-cap Hessian-weighted Gaussian quadratic residuals after the compact Hessian bound and intrinsic Gaussian centred-square estimates are supplied.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.avram_gb43_bounded_multiplier_centered_square_L2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H R : Ω → ℝ) (B K : ℝ)
    (hH : Measurable H) (hR : Measurable R)
    (hK : 0 ≤ K) (hHb : ∀ ω, |H ω| ≤ K)
    (hR2 : Integrable (fun ω => (R ω) ^ 2) P)
    (hB : (∫ ω, (R ω) ^ 2 ∂P) ≤ B) :
    Integrable (fun ω => (H ω * R ω) ^ 2) P ∧
      (∫ ω, (H ω * R ω) ^ 2 ∂P) ≤ K ^ 2 * B := by
  sorry
