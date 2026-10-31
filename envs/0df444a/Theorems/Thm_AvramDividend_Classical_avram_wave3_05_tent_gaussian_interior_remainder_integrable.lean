-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_gaussian_interior_remainder_integrable
-- name    : AvramDividend.Classical.avram_wave3_05_tent_gaussian_interior_remainder_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:40:33.210135+00:00
-- url     : https://prove2.me/theorems/e11ef020-55db-439d-9453-829faf4820f4
-- title:
--   Gaussian compensated interior Taylor remainder integrable with quadratic weighted L1 bound
-- statement:
--   The compensated Gaussian Taylor remainder along a negative-jump segment of length r is a triangular kernel. Under source-like positive-state curvature continuity, global measurability and exponentially weighted absolute L1 curvature, the positive-reserve integrated remainder is integrable with its sharp quadratic r²/2 bound. This genuinely proves both local interval and global positive-state integrability using joint measurability, convolution and Fubini.
-- source:
--   Pinned Mathlib 0df444a; fully inlined source remotely elaborated to sentinel with zero source compiler errors on 30 October 2026, candidate-probe job d416ddd3-d214-4266-8b21-64f4a722474e. Related to Avram-Palmowski-Pistorius (2007) Gaussian generator q-harmonicity.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_gaussian_interior_remainder_integrable
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F)
    (hF : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|)
      (Ioi r) volume ∧
    (∫ x in Ioi r, Real.exp (-θ * x) *
      |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by sorry
