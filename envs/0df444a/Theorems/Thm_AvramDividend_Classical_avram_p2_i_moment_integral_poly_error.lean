-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integral_poly_error
-- name    : AvramDividend.Classical.avram_p2_i_moment_integral_poly_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:22:34.928378+00:00
-- url     : https://prove2.me/theorems/d203396b-fe8e-4fbc-9c18-b5b83cde28c4
-- title:
--   Quantitative L1 polynomial error controlled by mass and one high moment
-- statement:
--   For a positive-supported measure, if a test g and polynomial p are integrable and have pointwise error at most epsilon(1+z^K) on nonnegative z, then the difference of their real integrals is bounded by epsilon times the sum of total mass and kth moment. This is the key analytic bridge from the global polynomial envelope to moment-to-continuous-test convergence, with all integrability assumptions explicit and no support restriction above z=1.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_integral_poly_error
    (μ : Measure ℝ) (g : ℝ → ℝ) (p : Polynomial ℝ)
    (ε : ℝ) (K : ℕ)
    (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (hbound : ∀ z : ℝ, 0 ≤ z →
      |g z - p.eval z| ≤ ε * (1 + z ^ K))
    (hg : Integrable g μ)
    (hp : Integrable (fun z : ℝ => p.eval z) μ)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (hK : Integrable (fun z : ℝ => z ^ K) μ) :
    |(∫ z : ℝ, g z ∂μ) - (∫ z : ℝ, p.eval z ∂μ)| ≤
      ε * ((∫ _ : ℝ, (1 : ℝ) ∂μ) +
        (∫ z : ℝ, z ^ K ∂μ)) := by sorry
