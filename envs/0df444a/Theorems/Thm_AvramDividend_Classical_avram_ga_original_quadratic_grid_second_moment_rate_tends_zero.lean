-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
-- name    : AvramDividend.Classical.avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:57:33.313913+00:00
-- url     : https://prove2.me/theorems/39efb963-40c6-442e-b8f0-3147d0f35c96
-- title:
--   Physical-mesh inverse-count quadratic noise second-moment bound implies L2 variance vanishing
-- statement:
--   For any measurable probability model and real stochastic variables U_m whose squared expectations satisfy E[U_m²]≤J/(m+1), the second moments tend to zero. This uses only nonnegativity of squared integrals and the pinned real reciprocal-rate limit. It is the final analytic implication of the original finite-cap physical-grid Hessian second-chaos martingale-difference variance theorem, allowing the compensated quadratic-noise error to disappear in the stopped cash estimate.
-- source:
--   Original physical finite-cap Gaussian stopped Ito–Stieltjes proof: combine the authentic original weighted-centred Gaussian quadratic mesh sum estimate with the vanishing-mesh second moment squeeze.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℕ → Ω → ℝ) (J : ℝ)
    (hRate : ∀ m : ℕ,
      (∫ ω, (U m ω) ^ 2 ∂P) ≤ J / ((m : ℝ) + 1)) :
    Tendsto (fun m : ℕ => ∫ ω, (U m ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
