-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integral_tendsto
-- name    : AvramDividend.Classical.avram_p2_i_moment_polynomial_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:24:18.562202+00:00
-- url     : https://prove2.me/theorems/1dcad04a-5f88-4949-8087-8ede6d3242f8
-- title:
--   Full polynomial integral convergence from monomial moments
-- statement:
--   Let a filter index measures on the real line and suppose every monomial is integrable for each measure and its integrals converge at every nonnegative integer degree. For any real polynomial p, the integral of its ordinary evaluation p.eval z then converges to the integral under the limiting measure. This packages the finite-sum bridge for direct use with the polynomial returned by Weierstrass and places no false support restriction on approximating measures.

import Mathlib
open MeasureTheory Filter Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_polynomial_integral_tendsto
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ) (p : Polynomial ℝ)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ))) :
    Tendsto (fun i => ∫ z : ℝ, p.eval z ∂μi i) l
      (nhds (∫ z : ℝ, p.eval z ∂μ)) := by sorry
